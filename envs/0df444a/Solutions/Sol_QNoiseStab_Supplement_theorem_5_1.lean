-- Prove2me | solution 1 for QNoiseStab.Supplement.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @blake-holman
-- created : 2026-11-26T04:04:18.862535+00:00
-- url     : https://prove2.me/submissions/e8e241d0-6417-47a6-b16b-555d84f2e037

import Mathlib
import Definitions.Def_QNoiseStab_Supplement_SpaceBoundedAlg_FitsInSpace
import Definitions.Def_QNoiseStab_Supplement_SpaceBoundedAlg_successProb
import Definitions.Def_QNoiseStab_Supplement_sortFun
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.ZMod.Basic
import Definitions.Def_QNoiseStab_noiseProb
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QNoiseStab_phaseQuery
import Definitions.Def_QNoiseStab_fourierWeight
import Definitions.Def_QNoiseStab_fourierVec
import Definitions.Def_QNoiseStab_successProb
import Definitions.Def_QNoiseStab_eventSet
import Definitions.Def_QNoiseStab_projLowDeg
import Definitions.Def_QNoiseStab_projEvent
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QNoiseStab_noiseOp
import Definitions.Def_QNoiseStab_noiseKernel
import Definitions.Def_QNoiseStab_coordNoise
import Definitions.Def_QNoiseStab_singleNoiseOp
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Algebra.Order.BigOperators.Expect

-- Paper.Query
section
namespace QuantumNoiseStability

/-- The phase of a query can depend on the basis label and one input symbol. -/
structure PhaseQuery (W ι G : Type*) where
  address : W → ι
  phase : W → G → ℂ
  norm_phase : ∀ w a, ‖phase w a‖ = 1

namespace PhaseQuery

variable {W ι G : Type*} [Fintype W]

noncomputable def operator (q : PhaseQuery W ι G) (x : ι → G) :
    EuclideanSpace ℂ W →ₗᵢ[ℂ] EuclideanSpace ℂ W where
  toFun v := WithLp.toLp 2 (fun w => q.phase w (x (q.address w)) * v w)
  map_add' u v := by ext w; exact mul_add _ _ _
  map_smul' c v := by ext w; exact mul_left_comm _ _ _
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    change (∑ w, ‖q.phase w (x (q.address w)) * v w‖ ^ 2) = _
    simp [q.norm_phase]

@[simp] theorem operator_apply (q : PhaseQuery W ι G) (x : ι → G)
    (v : EuclideanSpace ℂ W) (w : W) :
    q.operator x v w = q.phase w (x (q.address w)) * v w := rfl

end PhaseQuery
end QuantumNoiseStability
end

-- Paper.TimeSpace.Execution
section
/-!
# Quantum queries with intermediate outputs

A finite instrument may write any list of outputs. Subsequent steps can use only the
state in `W`. The history labels index the sum in the Born rule and are absent from
the input to each step. Subnormalized instruments also allow aborting a computation.
-/

noncomputable section

namespace QuantumNoiseStability.TimeSpace

abbrev State (W : Type*) := EuclideanSpace ℂ W

/-- An input-independent operation, with one Kraus operator for each recorded outcome. -/
structure Instrument (W O : Type) [Fintype W] where
  outcomes : ℕ
  kraus : Fin outcomes → State W →ₗ[ℂ] State W
  emit : Fin outcomes → List O
  subnormalized : ∀ v, ∑ j, ‖kraus j v‖ ^ 2 ≤ ‖v‖ ^ 2

inductive Step (W ι G O : Type) [Fintype W] where
  | op : Instrument W O → Step W ι G O
  | query : PhaseQuery W ι G → Step W ι G O

variable {W ι G O : Type} [Fintype W]

/-- A complete sequence of outcomes has a finite type depending on the program. -/
def Hist : List (Step W ι G O) → Type
  | [] => Unit
  | .op op :: rest => Fin op.outcomes × Hist rest
  | .query _ :: rest => Hist rest

instance instFintypeHist : (l : List (Step W ι G O)) → Fintype (Hist l)
  | [] => inferInstanceAs (Fintype Unit)
  | .op op :: rest =>
      haveI := instFintypeHist rest
      inferInstanceAs (Fintype (Fin op.outcomes × Hist rest))
  | .query _ :: rest => instFintypeHist rest


/-- The unnormalized linear evolution along a single history. -/
def branchMap : (l : List (Step W ι G O)) → (ι → G) → Hist l → State W →ₗ[ℂ] State W
  | [], _, _ => LinearMap.id
  | .op op :: rest, x, h => (branchMap rest x h.2).comp (op.kraus h.1)
  | .query q :: rest, x, h => (branchMap rest x h).comp (q.operator x).toLinearMap

def run (l : List (Step W ι G O)) (x : ι → G) (v : State W) (h : Hist l) : State W :=
  branchMap l x h v

/-- The ordered transcript of the write-only output tape. -/
def claims : (l : List (Step W ι G O)) → Hist l → List O
  | [], _ => []
  | .op op :: rest, h => op.emit h.1 ++ claims rest h.2
  | .query _ :: rest, h => claims rest h

def queries : List (Step W ι G O) → ℕ
  | [] => 0
  | .op _ :: rest => queries rest
  | .query _ :: rest => queries rest + 1

@[simp] theorem queries_nil : queries ([] : List (Step W ι G O)) = 0 := rfl
@[simp] theorem queries_op (op : Instrument W O) (rest : List (Step W ι G O)) :
    queries (.op op :: rest) = queries rest := rfl
@[simp] theorem queries_query (q : PhaseQuery W ι G) (rest : List (Step W ι G O)) :
    queries (.query q :: rest) = queries rest + 1 := rfl

theorem queries_append (a b : List (Step W ι G O)) :
    queries (a ++ b) = queries a + queries b := by
  induction a with
  | nil => simp
  | cons s a ih => cases s <;> simp [ih, Nat.add_right_comm]

/-- The probabilities of all histories sum to at most the mass of the initial state. -/
theorem sum_mass_run_le (l : List (Step W ι G O)) (x : ι → G) (v : State W) :
    ∑ h, ‖run l x v h‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  induction l generalizing v with
  | nil =>
    change ∑ _ : Unit, ‖v‖ ^ 2 ≤ ‖v‖ ^ 2
    simp
  | cons s rest ih =>
    cases s with
    | op op =>
      change (∑ h : Fin op.outcomes × Hist rest, ‖run rest x (op.kraus h.1 v) h.2‖ ^ 2) ≤ _
      rw [Fintype.sum_prod_type]
      exact (Finset.sum_le_sum fun j _ => ih (op.kraus j v)).trans (op.subnormalized v)
    | query q =>
      change ∑ h : Hist rest, ‖run rest x (q.operator x v) h‖ ^ 2 ≤ _
      simpa using ih (q.operator x v)

/-- Histories factor at any cut in the list of steps. -/
def histAppend : (a b : List (Step W ι G O)) → Hist (a ++ b) ≃ Hist a × Hist b
  | [], b => (Equiv.punitProd (Hist b)).symm
  | .op op :: a, b =>
      ((Equiv.refl (Fin op.outcomes)).prodCongr (histAppend a b)).trans
        (Equiv.prodAssoc (Fin op.outcomes) (Hist a) (Hist b)).symm
  | .query _ :: a, b => histAppend a b

theorem run_append (a b : List (Step W ι G O)) (x : ι → G) (v : State W)
    (h : Hist (a ++ b)) :
    run (a ++ b) x v h = run b x (run a x v (histAppend a b h).1) (histAppend a b h).2 := by
  induction a generalizing v with
  | nil => rfl
  | cons s a ih => cases s <;> exact ih _ _

theorem claims_append (a b : List (Step W ι G O)) (h : Hist (a ++ b)) :
    claims (a ++ b) h = claims a (histAppend a b h).1 ++ claims b (histAppend a b h).2 := by
  induction a with
  | nil => rfl
  | cons s a ih =>
    cases s with
    | op op =>
      change op.emit _ ++ claims (a ++ b) _ = (op.emit _ ++ claims a _) ++ _
      rw [ih, List.append_assoc]
      rfl
    | query q => exact ih _

theorem sum_hist_append {M : Type*} [AddCommMonoid M] (a b : List (Step W ι G O))
    (f : Hist (a ++ b) → M) :
    ∑ h, f h = ∑ h₁ : Hist a, ∑ h₂ : Hist b, f ((histAppend a b).symm (h₁, h₂)) := by
  calc ∑ h, f h = ∑ p : Hist a × Hist b, f ((histAppend a b).symm p) :=
        Fintype.sum_equiv (histAppend a b) _ _ (fun h => by simp)
    _ = _ := Fintype.sum_prod_type _

/-- Probability of a transcript event on a fixed input and initial state. -/
def eventMass (l : List (Step W ι G O)) (x : ι → G) (v : State W) (P : List O → Prop) : ℝ := by
  classical
  exact ∑ h, if P (claims l h) then ‖run l x v h‖ ^ 2 else 0

/-- Success on a uniformly random input. -/
def success [Fintype ι] [DecidableEq ι] [Fintype G] (l : List (Step W ι G O)) (v : State W)
    (P : (ι → G) → List O → Prop) : ℝ :=
  (Fintype.card (ι → G) : ℝ)⁻¹ * ∑ x, eventMass l x v (P x)

/-- A transcript event has probability at most the squared norm of the initial state. -/
theorem eventMass_le_norm_sq (l : List (Step W ι G O)) (x : ι → G) (v : State W)
    (P : List O → Prop) : eventMass l x v P ≤ ‖v‖ ^ 2 := by
  apply le_trans _ (sum_mass_run_le l x v)
  unfold eventMass
  exact Finset.sum_le_sum fun h _ => by split_ifs <;> first | rfl | positivity

/-- The average probability of any success event is at most one. -/
theorem success_le_one [Fintype ι] [DecidableEq ι] [Fintype G] [Nonempty G]
    (l : List (Step W ι G O)) (v : State W) (hv : ‖v‖ ^ 2 ≤ 1)
    (P : (ι → G) → List O → Prop) : success l v P ≤ 1 := by
  calc success l v P ≤ (Fintype.card (ι → G) : ℝ)⁻¹ * ∑ _ : ι → G, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun x _ => (eventMass_le_norm_sq l x v (P x)).trans hv) (by positivity)
    _ = 1 := by simp

end QuantumNoiseStability.TimeSpace
end
end

-- Paper.TimeSpace.Partition
section
/-! Contiguous partitions by query count. Intermediate measurements have zero query cost. -/

namespace QuantumNoiseStability.TimeSpace

variable {W ι G O : Type} [Fintype W]

/-! ## Chunking a step list into slices -/

/-- A step list with at least `t` query steps splits as `a ++ b` with exactly `t` query
steps in `a`. -/
theorem exists_split_queries :
    ∀ (l : List (Step W ι G O)) (t : ℕ), t ≤ queries l →
      ∃ a b, l = a ++ b ∧ queries a = t
  | [], t, ht => by
    refine ⟨[], [], rfl, ?_⟩
    simp at ht
    simp [ht]
  | s :: l, t, ht => by
    cases t with
    | zero => exact ⟨[], s :: l, rfl, rfl⟩
    | succ t' =>
      cases s with
      | op K =>
        simp only [queries_op] at ht
        obtain ⟨a, b, hab, ha⟩ := exists_split_queries l (t' + 1) ht
        exact ⟨Step.op K :: a, b, by rw [hab]; rfl, by simp [ha]⟩
      | query q =>
        simp only [queries_query] at ht
        obtain ⟨a, b, hab, ha⟩ := exists_split_queries l t' (by omega)
        exact ⟨Step.query q :: a, b, by rw [hab]; rfl, by simp [ha]⟩

/-- The number of slices of at most `t` queries each: `max 1 ⌈T / t⌉`. -/
def sliceCount (T t : ℕ) : ℕ := max 1 ((T + t - 1) / t)

theorem queries_flatten (cs : List (List (Step W ι G O))) :
    queries cs.flatten = (cs.map queries).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatten_cons, queries_append, ih, List.map_cons, List.sum_cons]

/-- **Chunking.** Every step list splits into contiguous slices with at most `t` query
steps each, using at most `max 1 ⌈T/t⌉` slices, where `T` is the number of query steps. -/
theorem exists_chunks (t : ℕ) (ht : 1 ≤ t) (l : List (Step W ι G O)) :
    ∃ cs : List (List (Step W ι G O)), cs.flatten = l ∧ (∀ c ∈ cs, queries c ≤ t) ∧
      cs.length ≤ sliceCount (queries l) t := by
  induction hN : queries l using Nat.strong_induction_on generalizing l with
  | _ N ih =>
    by_cases hle : queries l ≤ t
    · refine ⟨[l], by simp, ?_, ?_⟩
      · intro c hc
        rw [List.mem_singleton] at hc
        rw [hc]; exact hle
      · simp [sliceCount]
    · push Not at hle
      obtain ⟨a, b, hab, ha⟩ := exists_split_queries l t hle.le
      have hqb : queries b = queries l - t := by
        rw [hab, queries_append, ha] at *
        omega
      have hlt : queries b < N := by omega
      obtain ⟨cs, hflat, hcs, hlen⟩ := ih (queries b) hlt b rfl
      refine ⟨a :: cs, ?_, ?_, ?_⟩
      · rw [List.flatten_cons, hflat, hab]
      · intro c hc
        rw [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact ha.le
        · exact hcs c hc
      · rw [List.length_cons]
        unfold sliceCount at hlen ⊢
        rw [hqb] at hlen
        have h1 : 1 ≤ (queries l - t + t - 1) / t := by
          apply Nat.le_div_iff_mul_le (by omega) |>.mpr
          omega
        rw [max_eq_right h1] at hlen
        have h2 : (queries l - t + t - 1) / t + 1 = (queries l + t - 1) / t := by
          have : queries l + t - 1 = (queries l - t + t - 1) + 1 * t := by omega
          rw [this, Nat.add_mul_div_right _ _ (by omega)]
        have h3 : (queries l + t - 1) / t ≤ max 1 ((queries l + t - 1) / t) := le_max_right _ _
        rw [← hN]
        omega

end QuantumNoiseStability.TimeSpace
end

-- Paper.TimeSpace.Arithmetic
section
/-!
# Arithmetic of time-space lower bounds

The circuit-specific input is a bound on a segment's success probability and the
pigeonhole implication for complete success. The three application theorems derive time
lower bounds from these numerical inputs. The sorting and hashing theorems also use
a whole-computation short-query bound. The segment count is the one from
`TimeSpace.Partition`, including the final short segment.
-/

namespace QuantumNoiseStability.TimeSpace

/-- The segment count used in the sorting parameter bounds. -/
abbrev segmentCount := sliceCount

/-- If a successful computation needs more than `r * (k - 1)` outputs, one of its
segments produces at least `k` correct outputs. Here `q` bounds the probability
before advice, and `p` is the complete-success probability. -/
def SlicedBound (m k r S : ℕ) (p q : ℝ) : Prop :=
  r * (k - 1) < m → p ≤ r * (2 : ℝ) ^ S * q

theorem slicedBound_of_segment_probabilities {m k r S : ℕ} {p q : ℝ}
    (prob : Fin r → ℝ) (hpigeon : r * (k - 1) < m → p ≤ ∑ i, prob i)
    (hseg : ∀ i, prob i ≤ (2 : ℝ) ^ S * q) : SlicedBound m k r S p q := by
  intro h
  apply (hpigeon h).trans
  simpa [mul_assoc] using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin r))) (fun i _ => hseg i)

/-- The strict segment budget permits equality in the required success probability. -/
theorem output_count_of_exponential_bound {m k r S : ℕ} {p C b d ℓ : ℝ}
    (hslice : SlicedBound m k r S p (C * (2 : ℝ) ^ (-d)))
    (hbudget : r * C < (2 : ℝ) ^ b) (hexp : b + S + ℓ ≤ d)
    (hsucc : (2 : ℝ) ^ (-ℓ) ≤ p) : m ≤ r * (k - 1) := by
  by_contra! h
  have hlt : (r : ℝ) * (2 : ℝ) ^ S * (C * (2 : ℝ) ^ (-d)) < (2 : ℝ) ^ (-ℓ) := by
    calc _ = (r * C) * ((2 : ℝ) ^ (S : ℝ) * 2 ^ (-d)) := by rw [Real.rpow_natCast]; ring
         _ < 2 ^ b * (2 ^ (S : ℝ) * 2 ^ (-d)) :=
           mul_lt_mul_of_pos_right hbudget (by positivity)
         _ = (2 : ℝ) ^ (b + S + -d) := by
           rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
           ring
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  exact (not_lt_of_ge hsucc) ((hslice h).trans_lt hlt)

theorem sliceCount_le_of_queries_le {T t r : ℕ} (ht : 0 < t) (hr : 1 ≤ r)
    (h : T ≤ t * r) : sliceCount T t ≤ r :=
  max_le hr ((ceilDiv_le_iff_le_mul ht).2 h)

theorem sliceCount_le_queries {T t : ℕ} (hT : 0 < T) (ht : 0 < t) :
    sliceCount T t ≤ T :=
  sliceCount_le_of_queries_le ht hT (Nat.le_mul_of_pos_left _ ht)

/-- Enough outputs for the threshold `k` force at least two segments. This also
justifies absorbing the ceiling without a separate hypothesis `t ≤ T`. -/
theorem work_le_of_output_count {m k r T t : ℕ} (ht : 0 < t) (hk : 0 < k)
    (hkm : k ≤ m) (hr : r ≤ sliceCount T t) (hout : m ≤ r * (k - 1)) :
    m * t ≤ 2 * T * (k - 1) := by
  have htwo : 1 < r := by
    by_contra! h
    have := Nat.mul_le_mul_right (k - 1) h
    simp only [one_mul] at this
    omega
  have hr' : r ≤ T ⌈/⌉ t := by change r ≤ max 1 (T ⌈/⌉ t) at hr; omega
  have htT : t ≤ T := by
    by_contra! h
    have hle : T ⌈/⌉ t ≤ 1 := (ceilDiv_le_iff_le_mul ht).2 (by simpa using h.le)
    omega
  have hrt : r * t ≤ 2 * T := by
    have h := Nat.mul_le_mul_right t hr'
    rw [Nat.ceilDiv_eq_add_pred_div] at h
    have := Nat.div_mul_le_self (T + t - 1) t
    omega
  calc m * t ≤ (r * (k - 1)) * t := Nat.mul_le_mul_right _ hout
       _ = (r * t) * (k - 1) := by ring
       _ ≤ _ := Nat.mul_le_mul_right _ hrt

/-- Rounding a segment length down loses at most a factor of two once it reaches one. -/
theorem le_two_mul_floor {x : ℝ} (hx : 1 ≤ x) : x ≤ 2 * (⌊x⌋₊ : ℝ) := by
  have h : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).2 (by simpa using hx)
  have h' : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast h
  linarith [Nat.lt_floor_add_one x]

noncomputable section

/-- Query budget in Lemma 5.4, rounded down to an integer. -/
def sortingSegmentLength (α : ℝ) (k n : ℕ) : ℕ :=
  ⌊α * (k : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ)⌋₊

/-- Conversion of the segment output count in the small-space case of §5.2.
Here `L` is the rounded logarithmic factor. -/
theorem sorting_of_output_count {α : ℝ} {n k L T r : ℕ}
    (hk : 0 < k) (hL : 0 < L) (hcap : 8 * L * k ≤ n)
    (hlen : 1 ≤ α * (k : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ))
    (hr : r ≤ sliceCount T (sortingSegmentLength α k n))
    (hout : n ≤ r * (8 * L * k - 1)) :
    α * (n : ℝ) ^ (4 / 3 : ℝ) ≤ 32 * T * L * (k : ℝ) ^ (1 / 3 : ℝ) := by
  let t := sortingSegmentLength α k n
  have ht : 1 ≤ t := (Nat.le_floor_iff (by linarith : 0 ≤
    α * (k : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ))).2 (by simpa using hlen)
  have hw := work_le_of_output_count ht (by positivity) hcap hr hout
  have hw' : n * t ≤ 2 * T * (8 * L * k) :=
    hw.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have hreal : (n : ℝ) * t ≤ 2 * T * (8 * L * k) := by exact_mod_cast hw'
  have hf : α * (k : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) ≤ 2 * t :=
    le_two_mul_floor hlen
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  apply le_of_mul_le_mul_right (a := (k : ℝ) ^ (2 / 3 : ℝ)) _ (by positivity)
  rw [mul_assoc (32 * (T : ℝ) * L), ← Real.rpow_add hk', show (1 / 3 + 2 / 3 : ℝ) = 1 by norm_num,
    Real.rpow_one, show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num,
    Real.rpow_add_of_nonneg (Nat.cast_nonneg n) (by norm_num) (by norm_num), Real.rpow_one]
  linarith [mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg n)]

/-- Above the allowed range of `k` in Lemma 5.4, a linear query lower bound
already gives the same tradeoff. -/
theorem sorting_of_large_space {α : ℝ} {n k L T : ℕ} (hα : 0 ≤ α)
    (hlarge : α * n ≤ (k : ℝ) * (8 * L : ℝ) ^ 3) (hlinear : n ≤ 3 * T) :
    α ^ (1 / 3 : ℝ) * (n : ℝ) ^ (4 / 3 : ℝ) ≤ 32 * T * L * (k : ℝ) ^ (1 / 3 : ℝ) := by
  have hroot := Real.rpow_le_rpow (mul_nonneg hα (Nat.cast_nonneg n)) hlarge
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rw [Real.mul_rpow hα (Nat.cast_nonneg n), Real.mul_rpow (Nat.cast_nonneg k) (by positivity),
    show (1 / 3 : ℝ) = (↑(3 : ℕ) : ℝ)⁻¹ by norm_num,
    Real.pow_rpow_inv_natCast (by positivity) (by decide : (3 : ℕ) ≠ 0)] at hroot
  have h' : α ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) ≤
      (k : ℝ) ^ (1 / 3 : ℝ) * (8 * L) := by norm_num [one_div] at hroot ⊢; exact hroot
  have hT : (n : ℝ) ≤ 3 * T := by exact_mod_cast hlinear
  rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num,
    Real.rpow_add_of_nonneg (Nat.cast_nonneg n) (by norm_num) (by norm_num), Real.rpow_one]
  have h := mul_le_mul hT h' (by positivity) (by positivity)
  linarith [show 0 ≤ (T : ℝ) * L * (k : ℝ) ^ (1 / 3 : ℝ) by positivity]

/-- Proposition 3.7 supplies the bound for reading the input when `3T ≤ n`.
This arithmetic step compares it with the required success probability. -/
theorem linear_time_of_recovery_bound {n m T : ℕ} {p ℓ : ℝ} (hm : 2 ≤ m)
    (hℓ : ℓ < n / (15 : ℝ)) (hsucc : (2 : ℝ) ^ (-ℓ) ≤ p)
    (hshort : 3 * T ≤ n → p ≤ (m : ℝ) ^ (-(n : ℝ) / 15)) : n < 3 * T := by
  by_contra! h
  have hbase : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hprob := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 2) hbase
    (show -(n : ℝ) / 15 ≤ 0 by linarith [Nat.cast_nonneg (α := ℝ) n])
  exact (not_lt_of_ge hsucc) (((hshort h).trans hprob).trans_lt
    (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)))

/-- The numerical conversion in §5.2, with `k = A*S` and output threshold
`8*⌈u⌉*k`. The ratio `u` can use any logarithm convention for which the
short-segment bound holds. The constants `α` and `β` specify the query length
and the allowed range of `k`, respectively. The input recovery and sliced success
bounds are the two circuit-specific hypotheses. -/
theorem sorting_time_lower_bound_of_range {n m S T A : ℕ} {α β γ u ℓ p : ℝ}
    (hn : 1 < n) (hm : 2 ≤ m) (hS : 0 < S) (hreg : n ^ 2 ≤ 2 ^ S)
    (hA : 4 ≤ A) (hγ : 3 ≤ γ * A) (hα : 0 < α) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hsize : 1 ≤ α * (n : ℝ) ^ (1 / 3 : ℝ)) (hu : 1 ≤ u)
    (hℓS : ℓ ≤ S) (hℓn : ℓ < n / (15 : ℝ)) (hsucc : (2 : ℝ) ^ (-ℓ) ≤ p)
    (hshort : 3 * T ≤ n → p ≤ (m : ℝ) ^ (-(n : ℝ) / 15))
    (hslice : let k := A * S
      4 ≤ k → (k : ℝ) * (8 * (⌈u⌉₊ : ℝ)) ^ 3 ≤ β * n →
      SlicedBound n (8 * ⌈u⌉₊ * k) (sliceCount T (sortingSegmentLength α k n)) S p
        ((2 : ℝ) ^ (-(γ * k)))) :
    min α β * (n : ℝ) ^ (4 / 3 : ℝ) / (64 * (A : ℝ) ^ (1 / 3 : ℝ) *
      (S : ℝ) ^ (1 / 3 : ℝ) * u) ≤ T := by
  let k := A * S
  let L := ⌈u⌉₊
  let t := sortingSegmentLength α k n
  have hk4 : 4 ≤ k := hA.trans (Nat.le_mul_of_pos_right _ hS)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hL : 1 ≤ L := Nat.ceil_pos.2 (by linarith)
  have hlinear := linear_time_of_recovery_bound hm hℓn hsucc hshort
  have hmain : min α β * (n : ℝ) ^ (4 / 3 : ℝ) ≤
      32 * T * L * (k : ℝ) ^ (1 / 3 : ℝ) := by
    by_cases hlarge : β * n ≤ (k : ℝ) * (8 * L : ℝ) ^ 3
    · have hcoef := (min_le_right α β).trans
          (Real.self_le_rpow_of_le_one hβ.le hβ1 (by norm_num : (1 / 3 : ℝ) ≤ 1))
      exact (mul_le_mul_of_nonneg_right hcoef (by positivity)).trans
        (sorting_of_large_space hβ.le hlarge hlinear.le)
    by_cases hbig : n ^ 2 ≤ T
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.le
      have hpow : (n : ℝ) ^ (4 / 3 : ℝ) ≤ (n : ℝ) ^ 2 := by
        rw [← Real.rpow_natCast _ 2]
        exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      have hT : (n : ℝ) ^ 2 ≤ T := by exact_mod_cast hbig
      have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
      have hcoef := (min_le_right α β).trans hβ1
      calc _ ≤ 1 * (n : ℝ) ^ 2 := mul_le_mul hcoef hpow (by positivity) zero_le_one
           _ ≤ T := by simpa using hT
           _ ≤ 32 * T * L * (k : ℝ) ^ (1 / 3 : ℝ) := by
             have h := mul_le_mul hL' (Real.one_le_rpow hk1 (by norm_num : (0 : ℝ) ≤ 1/3))
               zero_le_one (Nat.cast_nonneg L)
             nlinarith [mul_le_mul_of_nonneg_left h (Nat.cast_nonneg T)]
    have hsmall := (lt_of_not_ge hlarge).le
    have hlen : 1 ≤ α * (k : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) := by
      calc 1 ≤ α * (n : ℝ) ^ (1 / 3 : ℝ) := hsize
           _ ≤ α * (n : ℝ) ^ (1 / 3 : ℝ) * (k : ℝ) ^ (2 / 3 : ℝ) :=
             le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hk1 (by norm_num))
           _ = _ := by ring
    have ht : 0 < t := (Nat.le_floor_iff (by linarith :
      0 ≤ α * (k : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ))).2 (by simpa using hlen)
    have hr : sliceCount T t < 2 ^ S :=
      (sliceCount_le_queries (by omega) ht).trans_lt ((lt_of_not_ge hbig).trans_le hreg)
    have hb : (sliceCount T t : ℝ) * 1 < (2 : ℝ) ^ (S : ℝ) := by
      rw [mul_one, Real.rpow_natCast]
      exact_mod_cast hr
    have hd : (S : ℝ) + S + ℓ ≤ γ * k := by
      dsimp [k]
      push_cast
      linarith [mul_le_mul_of_nonneg_right hγ (Nat.cast_nonneg S)]
    have hs := hslice hk4 hsmall
    have hout : n ≤ sliceCount T t * (8 * L * k - 1) :=
      output_count_of_exponential_bound (C := 1) (by simpa only [one_mul] using hs) hb hd hsucc
    have hcap : 8 * L * k ≤ n := by
      have hnat : (8 * L : ℝ) ≤ (8 * L : ℝ) ^ 3 :=
        le_self_pow₀ (by exact_mod_cast (show 1 ≤ 8 * L by omega)) (by decide)
      have h := (mul_le_mul_of_nonneg_left hnat (Nat.cast_nonneg k)).trans
        (hsmall.trans (mul_le_of_le_one_left (Nat.cast_nonneg n) hβ1))
      exact_mod_cast (by simpa [mul_comm] using h : (8 * (L : ℝ)) * k ≤ n)
    exact (mul_le_mul_of_nonneg_right (min_le_left α β) (by positivity)).trans
      (sorting_of_output_count (by omega) hL hcap hlen le_rfl hout)
  have hround : (L : ℝ) ≤ 2 * u := by linarith [Nat.ceil_lt_add_one (by linarith : 0 ≤ u)]
  have hkpow : (k : ℝ) ^ (1 / 3 : ℝ) = (A : ℝ) ^ (1 / 3 : ℝ) * (S : ℝ) ^ (1 / 3 : ℝ) := by
    simp [k, Real.mul_rpow]
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  apply (div_le_iff₀ (by positivity)).2
  rw [hkpow] at hmain
  have h := mul_le_mul_of_nonneg_right hround
    (show 0 ≤ 32 * (T : ℝ) * ((A : ℝ) ^ (1 / 3 : ℝ) * (S : ℝ) ^ (1 / 3 : ℝ)) by positivity)
  linarith

/-- Specialization when Lemma 5.4 uses the same constant for the query budget
and the admissible range of output thresholds. -/
theorem sorting_time_lower_bound {n m S T A : ℕ} {α γ u ℓ p : ℝ}
    (hn : 1 < n) (hm : 2 ≤ m) (hS : 0 < S) (hreg : n ^ 2 ≤ 2 ^ S)
    (hA : 4 ≤ A) (hγ : 3 ≤ γ * A) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsize : 1 ≤ α * (n : ℝ) ^ (1 / 3 : ℝ)) (hu : 1 ≤ u)
    (hℓS : ℓ ≤ S) (hℓn : ℓ < n / (15 : ℝ)) (hsucc : (2 : ℝ) ^ (-ℓ) ≤ p)
    (hshort : 3 * T ≤ n → p ≤ (m : ℝ) ^ (-(n : ℝ) / 15))
    (hslice : ∀ k : ℕ, 4 ≤ k → (k : ℝ) * (8 * (⌈u⌉₊ : ℝ)) ^ 3 ≤ α * n →
      SlicedBound n (8 * ⌈u⌉₊ * k) (sliceCount T (sortingSegmentLength α k n)) S p
        ((2 : ℝ) ^ (-(γ * k)))) :
    α * (n : ℝ) ^ (4 / 3 : ℝ) / (64 * (A : ℝ) ^ (1 / 3 : ℝ) *
      (S : ℝ) ^ (1 / 3 : ℝ) * u) ≤ T := by
  simpa only [min_self] using sorting_time_lower_bound_of_range hn hm hS hreg hA hγ hα hα hα1
    hsize hu hℓS hℓn hsucc hshort (hslice (A * S))

-- These expressions agree by definition with the budgets in Sorting.Parameters,
-- which imports the numeric conversion above.
local notation "widthFactor" => (fun n : ℕ => ⌈Real.log n / Real.log (Real.log n)⌉₊)
local notation "queryBudget" => (fun n k : ℕ =>
  ⌊(k : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) / 128⌋₊)

/-- Theorem 5.1 at the numeric interface of `Sorting.lemma54_parameters`.
Only the input recovery probability and the sliced probability implication for
`k = 36S` are required from the circuit. Both constants and the cutoff are explicit. -/
theorem sorting_log_time_lower_bound {n m S T : ℕ} {p : ℝ}
    (hn : 128 ^ 3 ≤ n) (hm : 2 ≤ m) (hreg : n ^ 2 ≤ 2 ^ S)
    (hsucc : (2 : ℝ) ^ (-min (S : ℝ)
      (n / (32 * (Real.log n / Real.log (Real.log n)) ^ 3))) ≤ p)
    (hshort : 3 * T ≤ n → p ≤ (m : ℝ) ^ (-(n : ℝ) / 15))
    (hslice : (36 * S) * (4096 * widthFactor n) ^ 3 ≤ n →
      SlicedBound n (8 * widthFactor n * (36 * S)) (sliceCount T (queryBudget n (36 * S)))
        S p ((2 : ℝ) ^ (-((36 * S : ℕ) : ℝ) / 12))) :
    (n : ℝ) ^ (4 / 3 : ℝ) * Real.log (Real.log n) /
      (512 ^ 3 * 64 * (36 : ℝ) ^ (1 / 3 : ℝ) * (S : ℝ) ^ (1 / 3 : ℝ) *
        Real.log n) ≤ T := by
  let u := Real.log n / Real.log (Real.log n)
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog := (Real.lt_log_iff_exp_lt hn0).2 (Real.exp_one_lt_three.trans_le hn')
  have hll := Real.log_pos hlog
  have hu : 1 ≤ u := by
    apply (one_le_div hll).2
    linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < Real.log n)]
  have hℓ : (n : ℝ) / (32 * u ^ 3) < n / 15 := by
    apply (div_lt_div_iff₀ (by positivity) (by norm_num)).2
    nlinarith only [hn0, mul_le_mul_of_nonneg_left (one_le_pow₀ hu (n := 3)) hn0.le]
  have hS : 0 < S := by
    by_contra! h
    have : S = 0 := by omega
    simp [this] at hreg
    nlinarith
  have hroot := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 128 ^ 3)
    (by exact_mod_cast hn : (128 : ℝ) ^ 3 ≤ n) (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rw [one_div, ← Nat.cast_ofNat (R := ℝ) (n := 3),
    Real.pow_rpow_inv_natCast (by norm_num) (by decide)] at hroot
  have hsize : 1 ≤ 1 / 128 * (n : ℝ) ^ (1 / 3 : ℝ) := by
    norm_num [one_div] at hroot ⊢
    linarith
  have hbound := sorting_time_lower_bound_of_range (A := 36) (γ := 1/12) (α := 1/128) (β := 1/512^3)
    (by omega : 1 < n) hm hS hreg (by decide) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hsize hu (min_le_left _ _) ((min_le_right _ _).trans_lt hℓ) hsucc hshort
  have happ : (min (1/128 : ℝ) (1/512^3)) * (n : ℝ) ^ (4/3 : ℝ) /
      (64 * (36 : ℝ) ^ (1/3 : ℝ) * (S : ℝ) ^ (1/3 : ℝ) * u) ≤ T := by
    apply hbound
    intro k _ hk
    have hrange : k * (4096 * widthFactor n) ^ 3 ≤ n := by
      change (k : ℝ) * (8 * (widthFactor n : ℝ)) ^ 3 ≤ 1 / 512^3 * n at hk
      exact_mod_cast (by linarith only [hk] :
        (k : ℝ) * (4096 * (widthFactor n : ℝ)) ^ 3 ≤ n)
    have ht : sortingSegmentLength (1/128) k n = queryBudget n k := by
      unfold sortingSegmentLength
      congr 1
      ring
    rw [ht]
    have he : -(1 / 12 * (k : ℝ)) = -(k : ℝ) / 12 := by ring
    rw [he]
    exact hslice hrange
  apply le_trans _ happ
  apply le_of_eq
  dsimp [u]
  rw [min_eq_right (by norm_num : (1 / 512 ^ 3 : ℝ) ≤ 1 / 128)]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- The final conversion for a fixed hash in §4.1. The whole-program short-query
bound uses `⌊m/32⌋` outputs. The slice bound uses `32S` outputs in the small-space
case. The success exponent `ℓ` may be any real up to `min S (m/1024)`. -/
theorem hashing_time_lower_bound {n m S T : ℕ} {α ℓ p : ℝ}
    (hm : 1024 ≤ m) (hmn : m ≤ n) (hreg : n ≤ 2 ^ S)
    (hα1 : α ≤ 1) (hlen : 1 ≤ α * n)
    (hℓS : ℓ ≤ S) (hℓm : ℓ ≤ m / (1024 : ℝ)) (hsucc : (2 : ℝ) ^ (-ℓ) ≤ p)
    (hshort : T ≤ ⌊α * n⌋₊ → p ≤ (2 : ℝ) ^ (-((m / 32 : ℕ) : ℝ) / 8))
    (hslice : 1024 * S ≤ m → SlicedBound m (32 * S) (sliceCount T ⌊α * n⌋₊) S p
      ((2 : ℝ) ^ (-((32 * S : ℕ) : ℝ) / 8))) :
    α * n * m ≤ 1024 * T * S := by
  let t := ⌊α * n⌋₊
  have hS : 0 < S := by
    by_contra! h
    have : S = 0 := by omega
    simp [this] at hreg
    omega
  have hf : (m : ℝ) ≤ 64 * ((m / 32 : ℕ) : ℝ) := by
    exact_mod_cast (show m ≤ 64 * (m / 32) by omega)
  have hT : t < T := by
    by_contra! h
    have hstrict : -(↑(m / 32) : ℝ) / 8 < -ℓ := by
      linarith [show (0 : ℝ) < m by exact_mod_cast (show 0 < m by omega)]
    exact (not_lt_of_ge hsucc) ((hshort h).trans_lt
      (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hstrict))
  have hlin : α * (n : ℝ) ≤ T := by
    have : t + 1 ≤ T := hT
    have h' : (t : ℝ) + 1 ≤ T := by exact_mod_cast this
    exact (Nat.lt_floor_add_one _).le.trans h'
  by_cases hsmall : 1024 * S ≤ m
  · by_cases hbig : n * m ≤ T
    · have hnm : (n : ℝ) * m ≤ T := by exact_mod_cast hbig
      have hS1 : (1 : ℝ) ≤ S := by exact_mod_cast hS
      calc _ ≤ 1 * (n : ℝ) * m := by gcongr
           _ ≤ T := by simpa using hnm
           _ ≤ 1024 * T * S := by nlinarith [mul_le_mul_of_nonneg_left hS1 (Nat.cast_nonneg T)]
    have ht : 0 < t := (Nat.le_floor_iff (by linarith : 0 ≤ α * n)).2 (by simpa using hlen)
    have hn2 : n * m ≤ 2 ^ (2 * S) := by
      rw [mul_comm 2 S, pow_mul, sq]
      exact Nat.mul_le_mul hreg (hmn.trans hreg)
    have hr := (sliceCount_le_queries (by omega : 0 < T) ht).trans_lt
      ((lt_of_not_ge hbig).trans_le hn2)
    have hb : (sliceCount T t : ℝ) * 1 < (2 : ℝ) ^ ((2 * S : ℕ) : ℝ) := by
      rw [mul_one, Real.rpow_natCast]
      exact_mod_cast hr
    have hd : ((2 * S : ℕ) : ℝ) + S + ℓ ≤ ((32 * S : ℕ) : ℝ) / 8 := by
      push_cast
      linarith
    have hs := hslice hsmall
    have hout := output_count_of_exponential_bound (C := 1) (by simpa [neg_div] using hs) hb hd hsucc
    have hw := work_le_of_output_count ht (by omega : 0 < 32 * S) (by omega : 32 * S ≤ m)
      le_rfl hout
    have hw' : m * t ≤ 2 * T * (32 * S) := hw.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have hw'' : (m : ℝ) * t ≤ 2 * T * (32 * S) := by exact_mod_cast hw'
    linarith [mul_le_mul_of_nonneg_right (le_two_mul_floor hlen) (Nat.cast_nonneg m),
      show 0 ≤ (T : ℝ) * S by positivity]
  · have hspace : (m : ℝ) ≤ 1024 * S := by exact_mod_cast (le_of_not_ge hsmall)
    linarith [mul_le_mul hlin hspace (Nat.cast_nonneg m) (Nat.cast_nonneg T)]

/-- The final conversion in §6.1 for integer segment length `h / 32`.
Rounding the length down gives the explicit constant `1 / 2048`.
The sliced bound is needed only at `k = ⌈16S/c⌉`; the numeric restrictions on
this choice are derived from the stated space bounds. -/
theorem matrix_time_lower_bound {n g h S T : ℕ} {c p : ℝ} (hn : 193 ≤ n)
    (hhn : h ≤ n) (hreg : n ≤ 2 ^ S) (hc : 0 < c) (hc1 : c ≤ 1)
    (hkg : ⌈16 * (S : ℝ) / c⌉₊ ≤ g) (hkh : 32 * ⌈16 * (S : ℝ) / c⌉₊ ≤ h)
    (hsucc : (2 : ℝ) ^ (-(S : ℝ)) ≤ p)
    (hslice : let k := ⌈16 * S / c⌉₊
      k ≤ g → 32 * k ≤ h → SlicedBound n k (sliceCount T (h / 32)) S p
        (3 * (2 : ℝ) ^ (-(c * k) / 4))) :
    c * n * h ≤ 2048 * T * S := by
  have hS : 0 < S := by
    by_contra! hh
    have : S = 0 := by omega
    simp [this] at hreg
    omega
  by_cases hbig : n * h ≤ T
  · have hnh : (n : ℝ) * h ≤ T := by exact_mod_cast hbig
    calc _ ≤ 1 * (n : ℝ) * h := by gcongr
         _ ≤ T := by simpa using hnh
         _ ≤ 2048 * T * S := by nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ S by exact_mod_cast hS) (Nat.cast_nonneg T)]
  let k := ⌈16 * S / c⌉₊
  have hkpos : 0 < k := Nat.ceil_pos.2 (by positivity)
  have hklo : 16 * (S : ℝ) ≤ (k : ℝ) * c :=
    (div_le_iff₀ hc).1 (Nat.le_ceil _)
  have hkhi : (k : ℝ) * c < 16 * S + c := by
    have hh := mul_lt_mul_of_pos_right
      (Nat.ceil_lt_add_one (by positivity : 0 ≤ 16 * (S : ℝ) / c)) hc
    rwa [add_mul, div_mul_cancel₀ _ hc.ne', one_mul] at hh
  have hround : h ≤ 64 * (h / 32) := by omega
  have hrbound : sliceCount T (h / 32) ≤ 64 * n := by
    apply sliceCount_le_of_queries_le (by omega) (by omega)
    calc T ≤ n * h := le_of_not_ge hbig
         _ ≤ n * (64 * (h / 32)) := Nat.mul_le_mul_left _ hround
         _ = _ := by ring
  have hr : sliceCount T (h / 32) * 3 < 2 ^ (2 * S) := by
    rw [mul_comm 2 S, pow_mul, sq]
    calc _ ≤ 64 * n * 3 := Nat.mul_le_mul_right _ hrbound
         _ < n * n := by nlinarith [Nat.mul_le_mul_left n hn]
         _ ≤ _ := Nat.mul_le_mul hreg hreg
  have hb : (sliceCount T (h / 32) : ℝ) * 3 < (2 : ℝ) ^ ((2 * S : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hr
  have hd : ((2 * S : ℕ) : ℝ) + S + S ≤ c * k / 4 := by push_cast; linarith
  have hs := hslice hkg hkh
  have hout := output_count_of_exponential_bound (by simpa [neg_div] using hs) hb hd hsucc
  have hw := work_le_of_output_count (by omega : 0 < h / 32) hkpos (by omega : k ≤ n) le_rfl hout
  have hnwork : n * h ≤ 128 * T * (k - 1) := by
    calc n * h ≤ n * (64 * (h / 32)) := Nat.mul_le_mul_left _ hround
         _ = 64 * (n * (h / 32)) := by ring
         _ ≤ 64 * (2 * T * (k - 1)) := Nat.mul_le_mul_left _ hw
         _ = _ := by ring
  have hw' : (n : ℝ) * h ≤ 128 * T * ((k : ℝ) - 1) := by
    have hh : (n : ℝ) * h ≤ 128 * T * ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hnwork
    simpa only [Nat.cast_sub hkpos, Nat.cast_one] using hh
  calc c * (n : ℝ) * h ≤ c * (128 * T * ((k : ℝ) - 1)) := by
         rw [mul_assoc]
         exact mul_le_mul_of_nonneg_left hw' hc.le
       _ = (128 * T) * ((k : ℝ) * c - c) := by ring
       _ ≤ (128 * T) * (16 * S) := by gcongr; linarith
       _ = _ := by ring

end

end QuantumNoiseStability.TimeSpace
end

-- Paper.TimeSpace.Encoding
section
/-! # Relabeling the input alphabet of a measured query program -/

noncomputable section

namespace QuantumNoiseStability

namespace PhaseQuery

variable {W ι X G : Type*}

/-- On an encoded symbol, apply the phase of the original symbol. -/
def reindex (q : PhaseQuery W ι X) (E : X ≃ G) : PhaseQuery W ι G where
  address := q.address
  phase w b := q.phase w (E.symm b)
  norm_phase w b := q.norm_phase w (E.symm b)

@[simp] theorem operator_reindex [Fintype W] (q : PhaseQuery W ι X) (E : X ≃ G) (x : ι → X) :
    (q.reindex E).operator (E ∘ x) = q.operator x := by
  ext v w
  simp [reindex, Function.comp_def]

end PhaseQuery

namespace TimeSpace

/-- Encode each input coordinate by the same alphabet equivalence. -/
def inputEquiv {ι X G : Type*} (E : X ≃ G) : (ι → X) ≃ (ι → G) :=
  Equiv.piCongrRight fun _ => E

@[simp] theorem inputEquiv_apply {ι X G : Type*} (E : X ≃ G) (x : ι → X) :
    inputEquiv E x = E ∘ x := rfl

@[simp] theorem inputEquiv_symm_apply {ι X G : Type*} (E : X ≃ G) (y : ι → G) :
    (inputEquiv E).symm y = E.symm ∘ y := rfl

/-- Choose a cyclic alphabet of the same cardinality as a finite nonempty alphabet. -/
def equivZMod (X : Type*) [Fintype X] [Nonempty X] : X ≃ ZMod (Fintype.card X) :=
  (Fintype.equivFin X).trans (ZMod.finEquiv _).toEquiv

variable {W ι X G O : Type} [Fintype W] (E : X ≃ G)

def Step.reindex : Step W ι X O → Step W ι G O
  | .op instr => .op instr
  | .query q => .query (q.reindex E)

def reindexSteps (l : List (Step W ι X O)) : List (Step W ι G O) :=
  l.map (Step.reindex E)

@[simp] theorem queries_reindex (l : List (Step W ι X O)) :
    queries (reindexSteps E l) = queries l := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    cases s with
    | op _ => exact ih
    | query _ => exact congrArg (· + 1) ih

/-- Match each instrument outcome with the same outcome in the encoded program. -/
def histReindex : (l : List (Step W ι X O)) → Hist l ≃ Hist (reindexSteps E l)
  | [] => Equiv.refl _
  | .op op :: l => (Equiv.refl (Fin op.outcomes)).prodCongr (histReindex l)
  | .query _ :: l => histReindex l

@[simp] theorem claims_reindex (l : List (Step W ι X O)) (h : Hist l) :
    claims (reindexSteps E l) (histReindex E l h) = claims l h := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    cases s with
    | op op => exact congrArg (op.emit h.1 ++ ·) (ih h.2)
    | query _ => exact ih h

@[simp] theorem branchMap_reindex (l : List (Step W ι X O)) (x : ι → X) (h : Hist l) :
    branchMap (reindexSteps E l) (E ∘ x) (histReindex E l h) = branchMap l x h := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    cases s with
    | op op => exact congrArg (·.comp (op.kraus h.1)) (ih h.2)
    | query q =>
      change Hist l at h
      change (branchMap (reindexSteps E l) (E ∘ x) (histReindex E l h)).comp
        ((q.reindex E).operator (E ∘ x)).toLinearMap = (branchMap l x h).comp _
      rw [ih, PhaseQuery.operator_reindex]

@[simp] theorem run_reindex (l : List (Step W ι X O)) (x : ι → X) (v : State W) (h : Hist l) :
    run (reindexSteps E l) (E ∘ x) v (histReindex E l h) = run l x v h := by
  simp [run]

@[simp] theorem eventMass_reindex (l : List (Step W ι X O)) (x : ι → X) (v : State W)
    (P : List O → Prop) : eventMass (reindexSteps E l) (E ∘ x) v P = eventMass l x v P := by
  classical
  unfold eventMass
  symm
  exact Fintype.sum_equiv (histReindex E l) _ _ (fun h => by simp)

/-- Uniform Born success is preserved when the event decodes its input before testing it. -/
@[simp] theorem success_reindex [Fintype ι] [DecidableEq ι] [Fintype X] [Fintype G]
    (l : List (Step W ι X O)) (v : State W) (P : (ι → X) → List O → Prop) :
    success (reindexSteps E l) v (fun y => P (E.symm ∘ y)) = success l v P := by
  unfold success
  rw [Fintype.card_congr (inputEquiv (ι := ι) E)]
  congr 1
  symm
  apply Fintype.sum_equiv (inputEquiv E)
  intro x
  simp [← Function.comp_assoc]

end TimeSpace
end QuantumNoiseStability
end
end

-- Paper.Noise.Kernel
section
noncomputable section

namespace QuantumNoiseStability.Noise

variable {ι G : Type*} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]

/-- The one-symbol transition probability of Proposition 3.1. -/
def symbolKernel (p : ℝ) (a b : G) : ℝ :=
  (if a = b then 1 - p else 0) + p / Fintype.card G

/-- The transition at coordinate `i`, with the identity transition outside `A`. -/
def coordKernel (A : Finset ι) (p : ℝ) (i : ι) (a b : G) : ℝ :=
  if i ∈ A then symbolKernel p a b else if a = b then 1 else 0

/-- Probability of obtaining `y` from `x` by resampling on `A` at rate `p`. -/
def kernel (A : Finset ι) (p : ℝ) (x y : ι → G) : ℝ :=
  ∏ i, coordKernel A p i (x i) (y i)

theorem kernel_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset ι) (x y : ι → G) :
    0 ≤ kernel A p x y := by
  apply Finset.prod_nonneg
  intro i _
  by_cases hi : i ∈ A <;> by_cases h : x i = y i <;>
    simp [coordKernel, symbolKernel, hi, h] <;> positivity

theorem kernel_comm (A : Finset ι) (p : ℝ) (x y : ι → G) :
    kernel A p x y = kernel A p y x := by
  unfold kernel
  exact Finset.prod_congr rfl fun i _ => by simp only [coordKernel, symbolKernel, eq_comm]

omit [Fintype ι] in
private theorem coordKernel_sum [Nonempty G] (A : Finset ι) (p : ℝ) (i : ι) (a : G) :
    ∑ b, coordKernel A p i a b = 1 := by
  by_cases hi : i ∈ A
  · have hcard : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [coordKernel, symbolKernel, hi, Finset.sum_add_distrib, mul_div_cancel₀ p hcard]
  · simp [coordKernel, hi]

theorem kernel_row_sum [Nonempty G] (A : Finset ι) (p : ℝ) (x : ι → G) :
    ∑ y, kernel A p x y = 1 := by
  unfold kernel
  rw [← Fintype.prod_sum (fun i b => coordKernel A p i (x i) b)]
  simp [coordKernel_sum]

theorem kernel_col_sum [Nonempty G] (A : Finset ι) (p : ℝ) (y : ι → G) :
    ∑ x, kernel A p x y = 1 := by
  simp_rw [kernel_comm A p _ y]
  exact kernel_row_sum A p y

/-- The number of coordinates in `A` on which the two inputs differ. -/
def hammingOn (A : Finset ι) (x y : ι → G) : ℕ :=
  (A.filter fun i => x i ≠ y i).card

/-- Proposition 3.2, including the zero probability of changing a fixed coordinate. -/
theorem kernel_eq_hamming (A : Finset ι) (p : ℝ) (x y : ι → G) :
    kernel A p x y = if ∀ i ∉ A, x i = y i then
      (1 - p + p / Fintype.card G) ^ (A.card - hammingOn A x y) *
        (p / Fintype.card G) ^ hammingOn A x y else 0 := by
  split_ifs with hagree
  · have hprod : kernel A p x y = ∏ i ∈ A,
        (if x i = y i then 1 - p + p / Fintype.card G else p / Fintype.card G) := by
      rw [← Fintype.prod_ite_mem]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ A
      · by_cases h : x i = y i <;> simp [coordKernel, symbolKernel, hi, h]
      · simp [coordKernel, hi, hagree i hi]
    rw [hprod, Finset.prod_ite]
    simp only [Finset.prod_const, hammingOn]
    have hc := Finset.card_filter_add_card_filter_not (s := A) (fun i => x i = y i)
    conv_rhs => rw [← hc, Nat.add_sub_cancel]
  · push Not at hagree
    obtain ⟨i, hi, hne⟩ := hagree
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [coordKernel, hi, hne])

/-- The Hamming formula when all coordinates are resampled. -/
theorem kernel_univ_eq_hamming (p : ℝ) (x y : ι → G) :
    kernel Finset.univ p x y =
      (1 - p + p / Fintype.card G) ^ (Fintype.card ι - hammingOn Finset.univ x y) *
        (p / Fintype.card G) ^ hammingOn Finset.univ x y := by
  simp [kernel_eq_hamming]

theorem kernel_eq_site {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (A : Finset (Fin n)) (p : ℝ) (x y : Fin n → X) :
    kernel A p x y = QNoiseStab.noiseKernel p A x y := by
  apply Finset.prod_congr rfl
  intro i _
  by_cases ha : i ∈ A <;> by_cases h : x i = y i <;>
    simp [coordKernel, symbolKernel, QNoiseStab.coordNoise, ha, h, div_eq_mul_inv, add_comm]

end QuantumNoiseStability.Noise
end
end

-- Paper.TimeSpace.EncodingNoise
section
/-! # Alphabet reindexing for restricted-coordinate resampling -/

namespace QuantumNoiseStability.Noise

/-- Relabeling both inputs preserves every restricted resampling transition probability. -/
@[simp] theorem kernel_reindex {ι X G : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype X] [DecidableEq X] [Fintype G] [DecidableEq G]
    (E : X ≃ G) (A : Finset ι) (p : ℝ) (x y : ι → X) :
    kernel A p (E ∘ x) (E ∘ y) = kernel A p x y := by
  simp only [kernel_eq_hamming, hammingOn, Function.comp_apply, ne_eq, E.apply_eq_iff_eq,
    Fintype.card_congr E]

end QuantumNoiseStability.Noise
end

-- Paper.Noise.Success
section
/-! # Uniform inputs and measured answers -/

noncomputable section

namespace QuantumNoiseStability.Noise

variable {K X : Type*} [Fintype K] [Fintype X]

/-- For each measurement outcome, sum its Born probabilities over the inputs on which it
is correct, and average over the uniform input. Outcomes can have overlapping events. -/
def success (amp : K → X → ℂ) (events : K → Finset X) : ℝ :=
  (Fintype.card X : ℝ)⁻¹ * ∑ k, ∑ x ∈ events k, ‖amp k x‖ ^ 2

theorem success_le_of_branch_bound [Nonempty X] (amp : K → X → ℂ) (events : K → Finset X)
    {c : ℝ} (hc : 0 ≤ c) (hnorm : ∀ x, ∑ k, ‖amp k x‖ ^ 2 ≤ 1)
    (hbranch : ∀ k, ∑ x ∈ events k, ‖amp k x‖ ^ 2 ≤ c * ∑ x, ‖amp k x‖ ^ 2) :
    success amp events ≤ c := by
  have hcard : 0 < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  have htotal : ∑ k, ∑ x, ‖amp k x‖ ^ 2 ≤ Fintype.card X := by
    rw [Finset.sum_comm]
    simpa using Finset.sum_le_sum (s := Finset.univ) fun x _ => hnorm x
  calc success amp events
      ≤ (Fintype.card X : ℝ)⁻¹ * ∑ k, c * ∑ x, ‖amp k x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hbranch k) (by positivity)
    _ ≤ (Fintype.card X : ℝ)⁻¹ * (c * Fintype.card X) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htotal hc) (by positivity)
    _ = c := by field_simp

/-- On a conceded input, the sum of the probabilities of all correct outcomes is at most one. -/
theorem success_le_sdiff_add [DecidableEq X] (amp : K → X → ℂ) (events : K → Finset X)
    (free : Finset X) (hnorm : ∀ x, ∑ k, ‖amp k x‖ ^ 2 ≤ 1) :
    success amp events ≤ success amp (fun k => events k \ free) +
      (Fintype.card X : ℝ)⁻¹ * free.card := by
  classical
  have hsplit (k : K) : ∑ x ∈ events k, ‖amp k x‖ ^ 2 ≤
      ∑ x ∈ events k \ free, ‖amp k x‖ ^ 2 + ∑ x ∈ free, ‖amp k x‖ ^ 2 := by
    have hdis : Disjoint (events k \ free) free :=
      Finset.disjoint_left.mpr fun _ h => (Finset.mem_sdiff.mp h).2
    rw [← Finset.sum_union hdis, Finset.sdiff_union_self_eq_union]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun _ _ _ => sq_nonneg _
  have hfree : ∑ k, ∑ x ∈ free, ‖amp k x‖ ^ 2 ≤ (free.card : ℝ) := by
    rw [Finset.sum_comm]
    simpa using Finset.sum_le_sum (s := free) fun x _ => hnorm x
  unfold success
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ∑ k, ∑ x ∈ events k, ‖amp k x‖ ^ 2
      ≤ ∑ k, (∑ x ∈ events k \ free, ‖amp k x‖ ^ 2 + ∑ x ∈ free, ‖amp k x‖ ^ 2) :=
        Finset.sum_le_sum fun k _ => hsplit k
    _ ≤ _ := by rw [Finset.sum_add_distrib]; exact add_le_add le_rfl hfree

end QuantumNoiseStability.Noise
end
end

-- Solutions.Corollary29
section
namespace QNoiseStab

section

variable {n d : ℕ}

/-- Finite sums of functions that each depend on at most `t` coordinates. -/
inductive JuntaSum (t : ℕ) : ((Fin n → ZMod d) → ℂ) → Prop where
  | junta (s : Finset (Fin n)) (hs : s.card ≤ t) (f : (Fin n → ZMod d) → ℂ)
      (hf : ∀ x y, (∀ i ∈ s, x i = y i) → f x = f y) : JuntaSum t f
  | sum {ι : Type} [Fintype ι] (f : ι → (Fin n → ZMod d) → ℂ)
      (hf : ∀ j, JuntaSum t (f j)) : JuntaSum t (fun x => ∑ j, f j x)

theorem JuntaSum.mul_unary {t : ℕ} {f : (Fin n → ZMod d) → ℂ} (hf : JuntaSum t f)
    (i : Fin n) (g : ZMod d → ℂ) : JuntaSum (t + 1) (fun x => g (x i) * f x) := by
  induction hf with
  | junta s hs f hf =>
    apply JuntaSum.junta (insert i s) ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ hs))
    intro x y h
    rw [h i (Finset.mem_insert_self ..), hf x y (fun j hj => h j (Finset.mem_insert_of_mem hj))]
  | sum f hf ih =>
    simp only [Finset.mul_sum]
    exact JuntaSum.sum _ ih

theorem JuntaSum.const (t : ℕ) (c : ℂ) :
    JuntaSum (n := n) (d := d) t (fun _ => c) :=
  .junta ∅ (by simp) _ (fun _ _ _ => rfl)

theorem JuntaSum.const_mul {t : ℕ} {f : (Fin n → ZMod d) → ℂ} (hf : JuntaSum t f) (c : ℂ) :
    JuntaSum t (fun x => c * f x) := by
  induction hf with
  | junta s hs f hf => exact .junta s hs _ (fun x y h => congrArg (c * ·) (hf x y h))
  | sum f hf ih =>
    simp only [Finset.mul_sum]
    exact .sum _ ih

theorem JuntaSum.matrix_mulVec {I J : Type} [Fintype J] {t : ℕ} (M : Matrix I J ℂ)
    (v : (Fin n → ZMod d) → J → ℂ) (h : ∀ j, JuntaSum t (fun x => v x j)) (i : I) :
    JuntaSum t (fun x => M.mulVec (v x) i) :=
  .sum _ (fun j => (h j).const_mul (M i j))

variable [NeZero d]

private lemma phase_act {W : Type} [Fintype W] [DecidableEq W] (ω : ℂ)
    (x : Fin n → ZMod d) (ψ : EuclideanSpace ℂ ((Fin n × ZMod d) × W))
    (p : (Fin n × ZMod d) × W) :
    QAlgorithms.act (Matrix.kronecker (phaseQuery ω x) (1 : Matrix W W ℂ)) ψ p =
      ω ^ (p.1.2 * x p.1.1).val * ψ p := by
  unfold phaseQuery Matrix.kronecker
  rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal]
  exact (Matrix.mulVec_diagonal _ _ _).trans (by simp)

private lemma state_juntaSum {W : Type} [Fintype W] [DecidableEq W] {T : ℕ}
    (ω : ℂ) (alg : QAlgorithms.QueryAlg (Fin n) (ZMod d) W T) (t : Fin (T + 1)) :
    ∀ q, JuntaSum t.val (fun x => alg.stateAt (phaseQuery ω x) t q) := by
  induction t using Fin.induction with
  | zero =>
    intro q
    exact JuntaSum.junta ∅ (by simp) _ (fun _ _ _ => rfl)
  | succ i ih =>
    intro q
    simp only [QAlgorithms.QueryAlg.stateAt, Fin.induction_succ]
    change JuntaSum (i.val + 1) (fun x => ∑ p, (alg.U i.succ : Matrix _ _ ℂ) q p *
      QAlgorithms.act (Matrix.kronecker (phaseQuery ω x) (1 : Matrix W W ℂ))
        (alg.stateAt (phaseQuery ω x) i.castSucc) p)
    simp only [phase_act, ← mul_assoc]
    exact JuntaSum.sum _ (fun p => JuntaSum.mul_unary (ih p) p.1.1
      (fun a => (alg.U i.succ : Matrix _ _ ℂ) q p * ω ^ (p.1.2 * a).val))

private lemma sum_star_ket {w : ZMod d} (hw : w ≠ 0) :
    ∑ a : ZMod d, star (fourierKet w a) = 0 := by
  have hchar (a : ZMod d) :
      Complex.exp (2 * Real.pi * Complex.I * (a.val : ℂ) / (d : ℂ)) = ZMod.stdAddChar a := by
    simpa using (ZMod.stdAddChar_coe (N := d) (a.val : ℤ)).symm
  have hzero : ∑ a : ZMod d, ZMod.stdAddChar (w * a) = 0 :=
    AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar d hw)
  rw [← star_sum]
  change star (∑ a : ZMod d, ((Real.sqrt d)⁻¹ : ℂ) * _) = 0
  simp only [hchar, ← Finset.mul_sum, hzero, mul_zero, star_zero]

private lemma junta_fourier_zero (s : Finset (Fin n)) (f : (Fin n → ZMod d) → ℂ)
    (hf : ∀ x y, (∀ j ∈ s, x j = y j) → f x = f y)
    (z : Fin n → ZMod d) (hz : s.card < fourierWeight z) :
    ∑ x, star (fourierVec z x) * f x = 0 := by
  classical
  obtain ⟨i, hzi, his⟩ := Finset.exists_mem_notMem_of_card_lt_card hz
  have hne : z i ≠ 0 := (Finset.mem_filter.mp hzi).2
  let e := Equiv.funSplitAt i (ZMod d)
  rw [← e.symm.sum_comp (fun x => star (fourierVec z x) * f x), Fintype.sum_prod_type_right]
  apply Finset.sum_eq_zero
  intro y _
  let x (a : ZMod d) := e.symm (a, y)
  have hxi (a) : x a i = a := by simp [x, e, Equiv.funSplitAt_symm_apply]
  have hoff (a) (j : Fin n) (hj : j ≠ i) : x a j = x 0 j := by
    simp [x, e, Equiv.funSplitAt_symm_apply, hj]
  have hproduct (a) : fourierVec z (x a) =
      fourierKet (z i) a * ∏ j ∈ Finset.univ.erase i, fourierKet (z j) (x 0 j) := by
    change ∏ j, fourierKet (z j) (x a j) = _
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), hxi]
    congr 1
    exact Finset.prod_congr rfl (fun j hj => by rw [hoff a j (Finset.ne_of_mem_erase hj)])
  have hf' (a) : f (x a) = f (x 0) := hf _ _ (fun j hj => hoff a j (fun h => his (h ▸ hj)))
  change ∑ a, star (fourierVec z (x a)) * f (x a) = 0
  simp only [hproduct, star_mul', hf', mul_assoc, ← Finset.sum_mul, sum_star_ket hne, zero_mul]

theorem JuntaSum.fourier_zero {t : ℕ} {f : (Fin n → ZMod d) → ℂ} (hf : JuntaSum t f)
    (z : Fin n → ZMod d) (hz : t < fourierWeight z) :
    ∑ x, star (fourierVec z x) * f x = 0 := by
  induction hf with
  | junta s hs f hf => exact junta_fourier_zero s f hf z (lt_of_le_of_lt hs hz)
  | sum f hf ih =>
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero (fun j _ => ih j)

end

-- The published statement assumes a root of unity. The degree bound uses only locality.
set_option linter.unusedVariables false in
/-- **Corollary 2.9** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query
Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256
814fe20e…), p.10, in the setting of p.9: "We focus on the domain X = Zm and the input
distribution being the uniform distribution on Xn"). The state of any quantum query algorithm
that makes at most `t` queries to its input is a linear combination of states whose input register
in the Fourier basis `|ẑ⟩` has the property that `z` contains at most `t` non-0 entries.

Stated for every `T`-query algorithm `alg` with phase queries `phaseQuery ω x` (`ω ^ d = 1`) on
inputs `x ∈ Z_dⁿ`, every number of queries `t ≤ T` (the intermediate state `alg.stateAt _ t`),
every computational basis state `q` of the algorithm registers `QPW`, and every frequency `z` with
more than `t` nonzero entries: `Σ_x conj(⟨x|ẑ⟩) · ⟨q|ψ_t^x⟩ = 0`.

**Formalization Note** For the uniform input the joint state after `t` queries is
`Σ_x d^{-n/2} |ψ_t^x⟩|x⟩`; its input-register component at the basis state `q` is
`φ_q = Σ_x d^{-n/2} ψ_t^x(q) |x⟩`, and `⟨ẑ|φ_q⟩` is `d^{-n/2}` times the displayed sum. "A linear
combination of `|q⟩ ⊗ |ẑ⟩` with at most `t` nonzero `z_i`" is exactly the vanishing of this sum for
every `q` and every `z` of weight `> t`. The Fourier basis uses the primitive root `exp(2πi/d)`;
the oracle root `ω` is any `d`-th root of unity. -/
theorem corollary_2_9 {W : Type} [Fintype W] [DecidableEq W] {n d T : ℕ} [NeZero d] (ω : ℂ)
    (hω : ω ^ d = 1) (alg : QAlgorithms.QueryAlg (Fin n) (ZMod d) W T) (t : Fin (T + 1))
    (q : (Fin n × ZMod d) × W) (z : Fin n → ZMod d) (hz : t.val < fourierWeight z) :
    ∑ x : Fin n → ZMod d, star (fourierVec z x) * alg.stateAt (phaseQuery ω x) t q = 0 := by
  exact JuntaSum.fourier_zero (state_juntaSum ω alg t q) z hz

end QNoiseStab
end

-- Solutions.QuerySuccess
section
/-! # Fourier projection, normalisation and summation of the output probabilities -/

noncomputable section

namespace QNoiseStab.SolutionSuccess

open Finset QAlgorithms

variable {n d T : ℕ} [NeZero d]

theorem projLow_fixed (t : ℕ) (v : EuclideanSpace ℂ (Fin n → ZMod d))
    (hcoeff : ∀ z, t < fourierWeight z → ∑ y, star (fourierVec z y) * v y = 0)
    (hcomplete : ∀ x y : Fin n → ZMod d,
      ∑ z, fourierVec z x * star (fourierVec z y) = if x = y then 1 else 0) :
    act (projLowDeg t) v = v := by
  classical
  ext x
  let coeff (z : Fin n → ZMod d) := ∑ y, star (fourierVec z y) * v y
  have expand (s : Finset (Fin n → ZMod d)) :
      (act (∑ z ∈ s, ketBra (fourierVec z)) v) x = ∑ z ∈ s, fourierVec z x * coeff z := by
    change ∑ y, (∑ z ∈ s, ketBra (fourierVec z)) x y * v y = _
    simp only [Matrix.sum_apply, ketBra, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp [coeff, Finset.mul_sum, mul_assoc]
  rw [projLowDeg, expand, Finset.sum_filter]
  calc ∑ z, (if fourierWeight z ≤ t then fourierVec z x * coeff z else 0) =
          ∑ z, fourierVec z x * coeff z := by
        apply sum_congr rfl
        intro z _
        split_ifs with hz
        · rfl
        · rw [show coeff z = 0 from hcoeff z (lt_of_not_ge hz), mul_zero]
    _ = ∑ y, (∑ z, fourierVec z x * star (fourierVec z y)) * v y := by
      simp only [coeff, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact sum_comm
    _ = v x := by simp_rw [hcomplete]; simp [ite_mul]

theorem event_projection_norm (E : Finset (Fin n → ZMod d)) (v : EuclideanSpace ℂ (Fin n → ZMod d)) :
    ‖act (projEvent E) v‖ ^ 2 = ∑ x ∈ E, ‖v x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  calc ∑ x, ‖act (projEvent E) v x‖ ^ 2 = ∑ x, if x ∈ E then ‖v x‖ ^ 2 else 0 := by
        apply sum_congr rfl
        intro x _
        by_cases hx : x ∈ E <;> simp [act, projEvent, Matrix.mulVec_diagonal, hx]
    _ = _ := by rw [← sum_filter]; simp

theorem act_product {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (A * B) v = act A (act B v) := by
  unfold act
  simp [Matrix.mulVec_mulVec]

theorem phase_norm {W : Type} [Fintype W] [DecidableEq W] (ω : ℂ) (hω : ω ^ d = 1)
    (x : Fin n → ZMod d) (v : EuclideanSpace ℂ ((Fin n × ZMod d) × W)) :
    ‖act (Matrix.kronecker (phaseQuery ω x) (1 : Matrix W W ℂ)) v‖ = ‖v‖ := by
  have hroot : ‖ω‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg ω) (NeZero.ne d)).mp
      (by simpa only [norm_pow, norm_one] using congrArg norm hω)
  let f (q : Fin n × ZMod d) := ω ^ (q.2 * x q.1).val
  have hmat : Matrix.kronecker (phaseQuery ω x) (1 : Matrix W W ℂ) =
      Matrix.diagonal (fun q : (Fin n × ZMod d) × W => f q.1) := by
    change Matrix.kronecker (Matrix.diagonal f) (1 : Matrix W W ℂ) = _
    unfold Matrix.kronecker
    rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal]
    simp
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hmat, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp [act, Matrix.mulVec_diagonal, f, norm_pow, hroot]

theorem state_norm {W : Type} [Fintype W] [DecidableEq W] (ω : ℂ) (hω : ω ^ d = 1)
    (alg : QueryAlg (Fin n) (ZMod d) W T) (x : Fin n → ZMod d) (t : Fin (T+1)) :
    ‖alg.stateAt (phaseQuery ω x) t‖ = 1 := by
  induction t using Fin.induction with
  | zero =>
    change ‖act _ alg.start‖ = 1
    exact (act_norm_of_mem_unitaryGroup (alg.U 0).property _).trans alg.start_unit
  | succ t ih =>
    change ‖act (alg.U t.succ : Matrix _ _ ℂ) (act (Matrix.kronecker (phaseQuery ω x) 1)
      (alg.stateAt (phaseQuery ω x) t.castSucc))‖ = 1
    rw [act_norm_of_mem_unitaryGroup (alg.U t.succ).property, phase_norm ω hω, ih]

theorem mass_sum {X K : Type} [Fintype X] [Fintype K] [DecidableEq X]
    (w : X → K → ℝ) (hw : ∀ x k, 0 ≤ w x k) (hone : ∀ x, ∑ k, w x k = 1)
    (free : Finset X) (R : X → K → Prop) [DecidableRel R] {c : ℝ}
    (hbound : ∀ k, ∑ x ∈ univ.filter (fun x => x ∉ free ∧ R x k), w x k ≤ c * ∑ x, w x k) :
    ∑ x, ∑ k, (if R x k then w x k else 0) ≤ c * Fintype.card X + free.card := by
  classical
  calc ∑ x, ∑ k, (if R x k then w x k else 0)
      ≤ ∑ x, ((∑ k, if x ∉ free ∧ R x k then w x k else 0) + if x ∈ free then 1 else 0) := by
        apply sum_le_sum
        intro x _
        by_cases hx : x ∈ free
        · simp only [hx, not_true_eq_false, false_and, if_false, sum_const_zero, if_true, zero_add]
          rw [← hone x]
          exact sum_le_sum fun k _ => by split_ifs <;> first | rfl | exact hw x k
        · simp [hx]
    _ = (∑ k, ∑ x ∈ univ.filter (fun x => x ∉ free ∧ R x k), w x k) + free.card := by
        rw [sum_add_distrib, sum_comm]
        simp [sum_filter]
    _ ≤ ∑ k, (c * ∑ x, w x k) + free.card := by
        exact add_le_add (sum_le_sum fun k _ => hbound k) le_rfl
    _ = c * Fintype.card X + free.card := by
        rw [← mul_sum, sum_comm]
        simp [hone]

end QNoiseStab.SolutionSuccess
end
end

-- Solutions.Fourier
section
namespace QNoiseStab.SolutionFourier

open scoped BigOperators

variable {m n : ℕ} [NeZero m]

private theorem ket_apply (z x : ZMod m) :
    fourierKet z x = (Real.sqrt m : ℂ)⁻¹ * ZMod.stdAddChar (z * x) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  rfl

private theorem star_char (x : ZMod m) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  change starRingEnd ℂ (ZMod.toCircle x : ℂ) = (ZMod.toCircle (-x) : ℂ)
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

theorem sum_ket_star (x y : ZMod m) :
    ∑ z, fourierKet z x * star (fourierKet z y) = if x = y then 1 else 0 := by
  have hs : (Real.sqrt m : ℂ) * (Real.sqrt m : ℂ) = (m : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg m)
  have hterm (z : ZMod m) :
      fourierKet z x * star (fourierKet z y) =
        (m : ℂ)⁻¹ * ZMod.stdAddChar (z * (x - y)) := by
    rw [ket_apply, ket_apply, star_mul, star_char, star_inv₀, Complex.star_def,
      Complex.conj_ofReal, mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, ← hs, mul_inv]
    ring
  simp only [hterm, ← Finset.mul_sum, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar m),
    sub_eq_zero, ZMod.card]
  split_ifs <;> simp [NeZero.ne m]

theorem sum_vec_star_vec (x y : Fin n → ZMod m) :
    ∑ z, fourierVec z x * star (fourierVec z y) = if x = y then 1 else 0 := by
  classical
  change ∑ z : Fin n → ZMod m, (∏ i, fourierKet (z i) (x i)) *
    star (∏ i, fourierKet (z i) (y i)) = _
  simp only [star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i t => fourierKet t (x i) * star (fourierKet t (y i)))]
  simp only [sum_ket_star, Fintype.prod_ite_zero, Finset.prod_const_one, ← funext_iff]

theorem sum_star_vec_vec (z s : Fin n → ZMod m) :
    ∑ x, star (fourierVec z x) * fourierVec s x = if z = s then 1 else 0 := by
  classical
  have symm (u v : Fin n → ZMod m) : fourierVec u v = fourierVec v u := by
    change (∏ i, fourierKet (u i) (v i)) = ∏ i, fourierKet (v i) (u i)
    simp only [ket_apply, mul_comm (u _) (v _)]
  simpa only [symm s _, symm z _, mul_comm, eq_comm] using sum_vec_star_vec s z

end QNoiseStab.SolutionFourier
end

-- Solutions.Lemma33
section
open scoped ComplexOrder

namespace QNoiseStab

/-- **Lemma 3.3** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity
and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…),
p.12). For `A ⊆ [n]`, `0 ≤ p < 1`, and every nonnegative integer `t`,
`Π_{B_t} ⪯ (1 − p)^{-t} T_p^A`.

**Formalization Note** The Loewner order `P ⪯ Q` is `(Q − P).PosSemidef`. `(1 − p)^{-t}` is
`((1 − p)^t)⁻¹` (positive since `p < 1`). `t` ranges over all of `ℕ`, including `t > n`. -/
theorem lemma_3_3 {n m : ℕ} [NeZero m] (A : Finset (Fin n)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (t : ℕ) :
    Matrix.PosSemidef (((((1 - p) ^ t)⁻¹ : ℝ) : ℂ) • (noiseOp p A : Matrix (Fin n → ZMod m)
      (Fin n → ZMod m) ℂ) - projLowDeg t) := by
  classical
  have hpos : 0 < 1 - p := sub_pos.mpr hp1
  have hunit : 1 - p ≤ 1 := by linarith
  unfold noiseOp projLowDeg
  rw [Finset.smul_sum, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Matrix.posSemidef_sum
  intro z _
  have hket : (ketBra (fourierVec z)).PosSemidef :=
    Matrix.posSemidef_vecMulVec_self_star (fun x => fourierVec z x)
  rw [smul_smul]
  by_cases hz : fourierWeight z ≤ t
  · have hcount : (A.filter fun i => z i ≠ 0).card ≤ fourierWeight z :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ A))
    have hpow := pow_le_pow_of_le_one hpos.le hunit (hcount.trans hz)
    have hscale : 1 ≤ ((1 - p) ^ t)⁻¹ * (1 - p) ^ (A.filter fun i => z i ≠ 0).card := by
      rw [← div_eq_inv_mul, le_div_iff₀ (pow_pos hpos t), one_mul]
      exact hpow
    rw [if_pos hz, ← one_smul ℂ (ketBra (fourierVec z))]
    -- Combine the scalar coefficients of this rank-one matrix.
    simp only [smul_smul, mul_one, ← sub_smul]
    apply hket.smul
    exact_mod_cast sub_nonneg.mpr hscale
  · rw [if_neg hz, sub_zero]
    apply hket.smul
    exact_mod_cast mul_nonneg (inv_nonneg.mpr (pow_nonneg hpos.le t)) (pow_nonneg hpos.le _)

end QNoiseStab
end

-- Solutions.Proposition31
section
namespace QNoiseStab

/-- **Proposition 3.1** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query
Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256
814fe20e…), p.11). For any `x, y ∈ [m]`,
`Pr[N_p(x) = y] = ⟨x| T_p |y⟩ = (1 − p) δ_{x,y} + p/m`, where `T_p = p |0̂⟩⟨0̂| + (1 − p) I`.

**Formalization Note** `[m]` is `ZMod m`; `Pr[N_p(x) = y]` is `coordNoise p x y`, cast to `ℂ`; the
matrix entry `⟨x|T_p|y⟩` is `singleNoiseOp p x y`. Both equalities are identities valid for every
real `p`. -/
theorem proposition_3_1 {m : ℕ} [NeZero m] (p : ℝ) (x y : ZMod m) :
    ((coordNoise p x y : ℝ) : ℂ) = singleNoiseOp p x y ∧
      singleNoiseOp p x y = ((1 - p) * (if x = y then 1 else 0) + p / m : ℝ) := by
  have hzero (a : ZMod m) : fourierKet (0 : ZMod m) a = ((Real.sqrt m : ℝ) : ℂ)⁻¹ := by
    simp [fourierKet]
  have hnorm : ((Real.sqrt m : ℝ) : ℂ) * (Real.sqrt m : ℝ) = (m : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg m : 0 ≤ (m : ℝ))
  have hentry : ketBra (fourierKet (0 : ZMod m)) x y = (m : ℂ)⁻¹ := by
    simp only [ketBra, Matrix.of_apply, hzero, star_inv₀, Complex.star_def, Complex.conj_ofReal,
      ← mul_inv, hnorm]
  have hformula : singleNoiseOp p x y = ((1 - p) * (if x = y then 1 else 0) + p / m : ℝ) := by
    simp only [singleNoiseOp, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hentry,
      Matrix.one_apply]
    push_cast
    split <;> simp_all [div_eq_mul_inv, add_comm]
  refine ⟨?_, hformula⟩
  rw [hformula]
  simp [coordNoise, ZMod.card, div_eq_mul_inv, add_comm]

end QNoiseStab
end

-- Solutions.Proposition32
section
namespace QNoiseStab

private theorem weighted_ket_sum {m : ℕ} [NeZero m] (p : ℝ) (x y : ZMod m) :
    ∑ z : ZMod m, (if z ≠ 0 then (1 - p : ℂ) else 1) *
      (fourierKet z x * star (fourierKet z y)) = coordNoise p x y := by
  let f (z : ZMod m) := fourierKet z x * star (fourierKet z y)
  have expand (z : ZMod m) :
      (if z ≠ 0 then (1 - p : ℂ) else 1) * f z =
        (if z = 0 then (p : ℂ) * f 0 else 0) + (1 - p) * f z := by
    by_cases hz : z = 0
    · subst z
      simp
      ring
    · simp [hz]
  change ∑ z, (if z ≠ 0 then (1 - p : ℂ) else 1) * f z = _
  simp only [expand, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [show ∑ z, f z = _ from SolutionFourier.sum_ket_star x y, (proposition_3_1 p x y).1]
  simp [singleNoiseOp, ketBra, Matrix.one_apply, f]

private theorem noiseOp_entry {n m : ℕ} [NeZero m] (p : ℝ) (A : Finset (Fin n))
    (x y : Fin n → ZMod m) : noiseOp p A y x = (noiseKernel p A x y : ℂ) := by
  classical
  let w (i : Fin n) (z : ZMod m) : ℂ :=
    if i ∈ A then (if z ≠ 0 then 1 - p else 1) else 1
  have weight (z : Fin n → ZMod m) :
      (((1 - p) ^ (A.filter fun i => z i ≠ 0).card : ℝ) : ℂ) = ∏ i, w i (z i) := by
    simp only [w, Fintype.prod_ite_mem]
    simp only [← Finset.prod_filter, Finset.prod_const,
      Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one]
  unfold noiseOp noiseKernel
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, weight, ketBra, Matrix.of_apply,
    fourierVec, WithLp.ofLp_toLp, star_prod, ← Finset.prod_mul_distrib, Complex.ofReal_prod]
  rw [← Fintype.prod_sum (fun i z => w i z * (fourierKet z (y i) * star (fourierKet z (x i))))]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ A
  · simp only [w, if_pos hi, weighted_ket_sum]
    simp [coordNoise, eq_comm]
  · simp only [w, if_neg hi, one_mul, SolutionFourier.sum_ket_star]
    by_cases hxy : x i = y i <;> simp [hxy, eq_comm]

/-- **Proposition 3.2** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query
Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256
814fe20e…), p.12). Let `x, y ∈ [m]ⁿ`. Then `Pr[N_p^A(x) = y] = ⟨y| T_p^A |x⟩`; if
`x_{[n]∖A} = y_{[n]∖A}` then
`Pr[N_p^A(x) = y] = (1 − p + p/m)^{|A| − d_A(x,y)} (p/m)^{d_A(x,y)}`, where
`d_A(x, y) = Σ_{i∈A} (1 − δ_{x_i,y_i}) = d(x, y)` is the Hamming distance between `x_A` and `y_A`;
when `x_{[n]∖A} ≠ y_{[n]∖A}`, `Pr[N_p^A(x) = y] = 0`.

**Formalization Note** `[m]` is `ZMod m`; `Pr[N_p^A(x) = y]` is `noiseKernel p A x y`; the matrix
entry `⟨y|T_p^A|x⟩` is `noiseOp p A y x`. `d_A(x, y)` is the number of `i ∈ A` with `x_i ≠ y_i`, so
the natural-number subtraction `|A| − d_A` is exact. The identities hold for every real `p`. -/
theorem proposition_3_2 {n m : ℕ} [NeZero m] (p : ℝ) (A : Finset (Fin n))
    (x y : Fin n → ZMod m) :
    let dA : ℕ := (A.filter fun i => x i ≠ y i).card
    ((noiseKernel p A x y : ℝ) : ℂ) = noiseOp p A y x ∧
      ((∀ i, i ∉ A → x i = y i) →
        noiseKernel p A x y = (1 - p + p / m) ^ (A.card - dA) * (p / m) ^ dA ∧
          dA = hammingDist x y) ∧
      ((∃ i, i ∉ A ∧ x i ≠ y i) → noiseKernel p A x y = 0) := by
  classical
  dsimp only
  refine ⟨(noiseOp_entry p A x y).symm, ?_, ?_⟩
  · intro hagree
    have hdist : A.filter (fun i => x i ≠ y i) = Finset.univ.filter (fun i => x i ≠ y i) := by
      ext i
      by_cases hi : i ∈ A <;> simp [hi, hagree]
    refine ⟨?_, congrArg Finset.card hdist⟩
    have hcoord (i : Fin n) : coordNoise p (x i) (y i) =
        if x i = y i then 1 - p + p / m else p / m := by
      by_cases h : x i = y i <;> simp [coordNoise, ZMod.card, h, div_eq_mul_inv, add_comm]
    have hcount := A.card_filter_add_card_filter_not (fun i => x i = y i)
    have hmatch : (A.filter fun i => x i = y i).card =
        A.card - (A.filter fun i => x i ≠ y i).card := Nat.eq_sub_of_add_eq hcount
    calc
      noiseKernel p A x y =
          ∏ i, (if i ∈ A then coordNoise p (x i) (y i) else 1) := by
        unfold noiseKernel
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi : i ∈ A <;> simp [hi, hagree]
      _ = _ := by
        rw [Fintype.prod_ite_mem]
        simp only [hcoord, Finset.prod_ite, Finset.prod_const, hmatch]
  · rintro ⟨i, hi, hxy⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi, hxy])

end QNoiseStab
end

-- Solutions.Theorem34
section
namespace QNoiseStab
namespace Compression34

open scoped BigOperators NNReal Matrix MatrixOrder ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- The maximum absolute row sum bounds the spectrum in the ℓ∞ operator norm.
open scoped Matrix.Norms.Operator in
private theorem spectrum_le_rows [Nonempty ι] (M : Matrix ι ι ℂ) {r b : ℝ}
    (hr : r ∈ spectrum ℝ M) (hb : 0 ≤ b) (hrow : ∀ i, ∑ j, ‖M i j‖ ≤ b) : r ≤ b := by
  refine (Real.le_norm_self r).trans ((spectrum.norm_le_norm_of_mem hr).trans ?_)
  rw [Matrix.linfty_opNorm_def]
  change (Finset.univ.sup fun i : ι => ∑ j : ι, ‖M i j‖₊) ≤ (⟨b, hb⟩ : ℝ≥0)
  apply Finset.sup_le
  intro i _
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_sum, coe_nnnorm]
  exact hrow i

open scoped Matrix.Norms.L2Operator

-- For a positive semidefinite matrix, the ℓ² operator norm belongs to this spectrum.
private theorem psd_norm_le_rows [Nonempty ι] (M : Matrix ι ι ℂ) (hM : M.PosSemidef)
    {b : ℝ} (hb : 0 ≤ b) (hrow : ∀ i, ∑ j, ‖M i j‖ ≤ b) : ‖M‖ ≤ b :=
  spectrum_le_rows M (CStarAlgebra.norm_mem_spectrum_of_nonneg hM.nonneg) hb hrow

private theorem projector_norm_sq (P Q : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q) :
    ‖P * Q‖ ^ 2 = ‖P * Q * P‖ := by
  rw [sq, ← CStarRing.norm_self_mul_star]
  change ‖P * Q * (P * Q)ᴴ‖ = _
  rw [Matrix.conjTranspose_mul, hQ.eq, hP.eq, ← mul_assoc, mul_assoc P Q Q, hQQ]

private theorem compression_bound [Nonempty ι] (P Q R : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (hRQ : (R - Q).PosSemidef) {b : ℝ} (hb : 0 ≤ b)
    (hrow : ∀ i, ∑ j, ‖(P * R * P) i j‖ ≤ b) (v : EuclideanSpace ℂ ι) :
    ‖QAlgorithms.act (P * Q) v‖ ^ 2 ≤ b * ‖v‖ ^ 2 := by
  have hQpos := Matrix.posSemidef_self_mul_conjTranspose Q
  rw [hQ.eq, hQQ] at hQpos
  have hpos := hQpos.mul_mul_conjTranspose_same P
  rw [hP.eq] at hpos
  have hle := hRQ.mul_mul_conjTranspose_same P
  rw [hP.eq, mul_sub, sub_mul] at hle
  have hcomp := Matrix.le_iff.mpr hle
  have hRpos : 0 ≤ P * R * P := hpos.nonneg.trans hcomp
  have hnorm : ‖P * Q‖ ^ 2 ≤ b := calc
    _ = _ := projector_norm_sq P Q hP hQ hQQ
    _ ≤ ‖P * R * P‖ := CStarAlgebra.norm_le_norm_of_nonneg_of_le hpos.nonneg hcomp
    _ ≤ b := psd_norm_le_rows _ (Matrix.nonneg_iff_posSemidef.mp hRpos) hb hrow
  calc
    _ ≤ (‖P * Q‖ * ‖v‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (Matrix.l2_opNorm_mulVec (P * Q) v) 2
    _ ≤ _ := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hnorm (sq_nonneg _)

variable {n m : ℕ} [NeZero m]
private theorem lowDeg_hermitian (t : ℕ) :
    (projLowDeg (n := n) (m := m) t).IsHermitian := by
  change (∑ z ∈ _, ketBra (fourierVec z))ᴴ = _
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro z _
  change (Matrix.vecMulVec (WithLp.ofLp (fourierVec z)) (star (WithLp.ofLp (fourierVec z))))ᴴ = _
  rw [Matrix.conjTranspose_vecMulVec, star_star]
  rfl

private theorem lowDeg_idempotent (t : ℕ) :
    projLowDeg (n := n) (m := m) t * projLowDeg t = projLowDeg t := by
  classical
  have hprod (z s : Fin n → ZMod m) :
      ketBra (fourierVec z) * ketBra (fourierVec s) =
        if z = s then ketBra (fourierVec z) else 0 := by
    change Matrix.vecMulVec _ (star (WithLp.ofLp (fourierVec z))) *
      Matrix.vecMulVec (WithLp.ofLp (fourierVec s)) _ = _
    rw [Matrix.vecMulVec_mul_vecMulVec]
    change Matrix.vecMulVec _ ((∑ x, star (fourierVec z x) * fourierVec s x) • _) = _
    rw [SolutionFourier.sum_star_vec_vec]
    split_ifs with h
    · subst s
      rw [one_smul]
      rfl
    · simp
  unfold projLowDeg
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  simp_rw [Finset.mul_sum, hprod]
  simp [hz]

omit [NeZero m] in
private theorem event_hermitian (E : Finset (Fin n → ZMod m)) : (projEvent E).IsHermitian := by
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  funext x
  change star (if x ∈ E then (1 : ℂ) else 0) = _
  split_ifs <;> simp_all

private theorem kernel_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (A : Finset (Fin n))
    (x y : Fin n → ZMod m) : 0 ≤ noiseKernel p A x y := by
  apply Finset.prod_nonneg
  intro i _
  have hp : 0 ≤ 1 - p := sub_nonneg.mpr hp1.le
  simp only [coordNoise]
  split_ifs <;> positivity

private theorem kernel_symm (p : ℝ) (A : Finset (Fin n)) (x y : Fin n → ZMod m) :
    noiseKernel p A y x = noiseKernel p A x y := by
  unfold noiseKernel
  apply Finset.prod_congr rfl
  intro i _
  simp only [coordNoise, @eq_comm _ (y i) (x i)]

private theorem event_rows (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (A : Finset (Fin n))
    (E : Finset (Fin n → ZMod m)) {β c : ℝ} (hβ0 : 0 ≤ β) (hc : 0 ≤ c)
    (hβ : ∀ x ∈ E, noiseProb p A x E ≤ β)
    (x : Fin n → ZMod m) :
    ∑ y, ‖(projEvent E * ((c : ℂ) • noiseOp (m := m) p A) * projEvent E) x y‖ ≤ c * β := by
  classical
  simp only [projEvent, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  by_cases hx : x ∈ E
  · simp only [hx, if_true, one_mul]
    calc
      _ = ∑ y, if y ∈ E then c * noiseKernel p A x y else 0 := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : y ∈ E
        · simp [hy, ← (proposition_3_2 p A y x).1, kernel_symm p A x y, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hc, abs_of_nonneg (kernel_nonneg p hp0 hp1 A x y)]
        · simp [hy]
      _ = c * noiseProb p A x E := by simp [noiseProb, Finset.mul_sum]
      _ ≤ c * β := mul_le_mul_of_nonneg_left (hβ x hx) hc
  · simpa [hx] using mul_nonneg hc hβ0

end Compression34
open Compression34

-- The platform includes ht, while Lemma 3.3 applies to every natural degree bound.
set_option linter.unusedVariables false in
/-- **Theorem 3.4** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query
Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256
814fe20e…), p.12). Let `A ⊆ [n]` and `E ⊆ [m]ⁿ` be some event. If `Π_E` is the projection onto the
input states that correspond to `E`, then for `0 ≤ t ≤ n`,
`‖Π_E Π_{B_t}‖² ≤ (1 − p)^{-t} max_{x∈E} Pr[N_p^A(x) ∈ E]`.

**Formalization Note** `[m]` is `ZMod m`. The range `0 ≤ p < 1` is that of Lemma 3.3, which the
proof applies (`N_p^A` is a random variable for `p ∈ [0, 1]`, and `(1 − p)^{-t}` is undefined at
`p = 1`). The squared operator norm is stated in its equivalent pointwise form
`‖Π_E Π_{B_t} ψ‖² ≤ c ‖ψ‖²` for every vector `ψ`. The maximum is encoded by any `β ≥ 0` bounding
`Pr[N_p^A(x) ∈ E]` for every `x ∈ E` (the maximum itself is such a `β`, and `max ∅ = 0`). -/
theorem theorem_3_4 {n m : ℕ} [NeZero m] (A : Finset (Fin n)) (E : Finset (Fin n → ZMod m))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (t : ℕ) (ht : t ≤ n) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ∀ x ∈ E, noiseProb p A x E ≤ β) (ψ : EuclideanSpace ℂ (Fin n → ZMod m)) :
    ‖QAlgorithms.act (projEvent E * projLowDeg t) ψ‖ ^ 2 ≤
      ((1 - p) ^ t)⁻¹ * β * ‖ψ‖ ^ 2 := by
  have hc : 0 ≤ ((1 - p) ^ t)⁻¹ := inv_nonneg.mpr (pow_nonneg (sub_nonneg.mpr hp1.le) _)
  exact compression_bound (projEvent E) (projLowDeg t) _ (event_hermitian E)
    (lowDeg_hermitian t) (lowDeg_idempotent t) (lemma_3_3 A p hp0 hp1 t)
    (mul_nonneg hc hβ0) (event_rows p hp0 hp1 A E hβ0 hc hβ) ψ

end QNoiseStab
end

-- Paper.TimeSpace.MeasuredNoise
section
noncomputable section
namespace QuantumNoiseStability.TimeSpace

variable {W ι G O : Type} [Fintype W] [Fintype ι] [DecidableEq ι] [Fintype G]

/-- Inputs on which a particular transcript is successful. -/
def eventInputs (P : (ι → G) → List O → Prop) (out : List O) : Finset (ι → G) := by
  classical
  exact Finset.univ.filter (fun x => P x out)

@[simp] theorem mem_eventInputs (P : (ι → G) → List O → Prop) (out : List O) (x : ι → G) :
    x ∈ eventInputs P out ↔ P x out := by classical simp [eventInputs]

/-- Measuring the workspace at the end refines every history into pairs of an instrument
history and a final basis state. Summing these Born weights gives the original event. -/
theorem success_eq_branch (l : List (Step W ι G O)) (v : State W) (P : (ι → G) → List O → Prop) :
    success l v P = Noise.success
      (fun (b : Hist l × W) x => run l x v b.1 b.2)
      (fun b => eventInputs P (claims l b.1)) := by
  classical
  unfold success Noise.success
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [eventInputs, Finset.sum_filter, eventMass]
  calc ∑ x, ∑ h, (if P x (claims l h) then ‖run l x v h‖ ^ 2 else 0) =
        ∑ x, ∑ h, ∑ w, (if P x (claims l h) then ‖run l x v h w‖ ^ 2 else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro h _
          by_cases he : P x (claims l h) <;> simp [he, EuclideanSpace.norm_sq_eq]
    _ = _ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

omit [Fintype ι] [DecidableEq ι] [Fintype G] in
theorem branch_mass_le_one (l : List (Step W ι G O)) (v : State W)
    (hv : ‖v‖ ^ 2 ≤ 1) (x : ι → G) :
    ∑ b : Hist l × W, ‖run l x v b.1 b.2‖ ^ 2 ≤ 1 := by
  simp only [Fintype.sum_prod_type, ← EuclideanSpace.norm_sq_eq]
  exact (sum_mass_run_le _ _ _).trans hv

variable {n d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem degree_run (l : List (Step W (Fin n) (ZMod d) O)) (h : Hist l)
    {t : ℕ} (u : (Fin n → ZMod d) → State W)
    (hu : ∀ w, QNoiseStab.JuntaSum t (fun x => u x w)) (w : W) :
    QNoiseStab.JuntaSum (t + queries l) (fun x => run l x (u x) h w) := by
  classical
  induction l generalizing t u with
  | nil => simpa [queries, run, branchMap] using hu w
  | cons step rest ih =>
    cases step with
    | op instr =>
      apply ih h.2 (fun x => instr.kraus h.1 (u x))
      intro j
      let M : Matrix W W ℂ := Matrix.toEuclideanLin.symm (instr.kraus h.1)
      have heq : Matrix.toEuclideanLin M = instr.kraus h.1 := LinearEquiv.apply_symm_apply _ _
      rw [← heq]
      exact QNoiseStab.JuntaSum.matrix_mulVec M (fun x j => u x j) hu j
    | query q =>
      have hq (j : W) : QNoiseStab.JuntaSum (t + 1) (fun x => q.operator x (u x) j) :=
        (hu j).mul_unary (q.address j) (q.phase j)
      change QNoiseStab.JuntaSum (t + (queries rest + 1)) _
      rw [show t + (queries rest + 1) = (t + 1) + queries rest by omega]
      exact ih h (fun x => q.operator x (u x)) hq

private theorem measured_cyclic (l : List (Step W (Fin n) (ZMod d) O)) (v : State W)
    (hv : ‖v‖ ^ 2 ≤ 1) (P : (Fin n → ZMod d) → List O → Prop) (A : Finset (Fin n))
    {p β : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ : 0 ≤ β)
    (hrow : ∀ out x, P x out → ∑ y ∈ eventInputs P out, Noise.kernel A p x y ≤ β) :
    success l v P ≤ ((1 - p) ^ queries l)⁻¹ * β := by
  classical
  rw [success_eq_branch]
  apply Noise.success_le_of_branch_bound _ _ (mul_nonneg (by positivity) hβ) (branch_mass_le_one l v hv)
  intro b
  let E := eventInputs P (claims l b.1)
  let ψ : EuclideanSpace ℂ (Fin n → ZMod d) := WithLp.toLp 2 (fun x => run l x v b.1 b.2)
  let t := min (queries l) n
  have deg : QNoiseStab.JuntaSum (queries l) (fun x => ψ x) := by
    simpa [ψ] using degree_run l b.1 (t := 0) (fun _ => v)
      (fun w => QNoiseStab.JuntaSum.const 0 (v w)) b.2
  have fixed := QNoiseStab.SolutionSuccess.projLow_fixed t ψ (fun z hz => by
    apply deg.fourier_zero
    have hw : QNoiseStab.fourierWeight z ≤ n := by
      simpa [QNoiseStab.fourierWeight] using
        (Finset.card_le_univ (Finset.univ.filter (fun i => z i ≠ 0)))
    dsimp [t] at hz
    omega) QNoiseStab.SolutionFourier.sum_vec_star_vec
  have rows (x) (hx : x ∈ E) : QNoiseStab.noiseProb p A x E ≤ β := by
    simpa only [QNoiseStab.noiseProb, ← Noise.kernel_eq_site] using
      hrow (claims l b.1) x ((mem_eventInputs _ _ _).mp hx)
  have main := QNoiseStab.theorem_3_4 A E p hp0.le hp1 t (min_le_right _ _) β hβ rows ψ
  rw [QNoiseStab.SolutionSuccess.act_product, fixed, QNoiseStab.SolutionSuccess.event_projection_norm,
    EuclideanSpace.norm_sq_eq] at main
  have hc : ((1-p)^t)⁻¹ ≤ ((1-p)^queries l)⁻¹ := by
    simp only [← inv_pow]
    exact pow_le_pow_right₀ ((one_le_inv₀ (by linarith : 0 < 1-p)).mpr (by linarith))
      (min_le_left _ _)
  exact main.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hβ)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))

private theorem event_row_reindex {X : Type} [Fintype X] [DecidableEq X] [DecidableEq G]
    (E : X ≃ G) (P : (ι → X) → List O → Prop) (out : List O) (A : Finset ι) (p : ℝ)
    (x : ι → X) :
    ∑ z ∈ eventInputs (fun z => P (E.symm ∘ z)) out, Noise.kernel A p (E ∘ x) z =
      ∑ y ∈ eventInputs P out, Noise.kernel A p x y := by
  classical
  simp only [eventInputs, Finset.sum_filter]
  symm
  apply Fintype.sum_equiv (inputEquiv E)
  intro y
  change (if P y out then _ else _) = (if P (E.symm ∘ E ∘ y) out then _ else _)
  simp [← Function.comp_assoc]

private theorem measured_noise_reindex {X : Type} [Fintype X] [DecidableEq X]
    (E : X ≃ ZMod d)
    (l : List (Step W (Fin n) X O)) (v : State W) (hv : ‖v‖ ^ 2 ≤ 1)
    (P : (Fin n → X) → List O → Prop) (A : Finset (Fin n)) {p β : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hβ : 0 ≤ β)
    (hrow : ∀ out x, P x out → ∑ y ∈ eventInputs P out, Noise.kernel A p x y ≤ β) :
    success l v P ≤ ((1 - p) ^ queries l)⁻¹ * β := by
  let P' := fun (z : Fin n → ZMod d) out => P (E.symm ∘ z) out
  have rows (out : List O) (z : Fin n → ZMod d) (hz : P' z out) :
      ∑ y ∈ eventInputs P' out, Noise.kernel A p z y ≤ β := by
    obtain ⟨x, rfl⟩ := (inputEquiv E).surjective z
    change ∑ y ∈ eventInputs P' out, Noise.kernel A p (E ∘ x) y ≤ β
    rw [event_row_reindex E P out A p x]
    exact hrow out x (by simpa only [P', inputEquiv_apply, ← Function.comp_assoc,
      E.symm_comp_self, Function.id_comp] using hz)
  rw [← success_reindex E l v P, ← queries_reindex E l]
  exact measured_cyclic (reindexSteps E l) v hv P' A hp0 hp1 hβ rows

/-- Theorem 3.5 for any finite nonempty alphabet and arbitrary measured transcripts.
The stability premise only ranges over the inputs on which the transcript is correct. -/
theorem measured_success_le_noise [Nonempty G] [DecidableEq G]
    (l : List (Step W (Fin n) G O)) (v : State W) (hv : ‖v‖ ^ 2 ≤ 1)
    (P : (Fin n → G) → List O → Prop) (A : Finset (Fin n)) {p β : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hβ : 0 ≤ β)
    (hrow : ∀ out x, P x out → ∑ y ∈ eventInputs P out, Noise.kernel A p x y ≤ β) :
    success l v P ≤ ((1 - p) ^ queries l)⁻¹ * β := by
  have : NeZero (Fintype.card G) := ⟨Fintype.card_ne_zero⟩
  exact measured_noise_reindex (equivZMod G) l v hv P A hp0 hp1 hβ hrow

/-- Removing conceded inputs costs at most their probability under the uniform law. -/
theorem success_le_remove_inputs [DecidableEq G] (l : List (Step W (Fin n) G O)) (v : State W)
    (hv : ‖v‖ ^ 2 ≤ 1) (P : (Fin n → G) → List O → Prop) (free : Finset (Fin n → G)) :
    success l v P ≤ success l v (fun x out => P x out ∧ x ∉ free) +
      (Fintype.card (Fin n → G) : ℝ)⁻¹ * free.card := by
  classical
  let amp (b : Hist l × W) (x : Fin n → G) := run l x v b.1 b.2
  let events (b : Hist l × W) := eventInputs P (claims l b.1)
  have he (b : Hist l × W) : events b \ free =
      eventInputs (fun x out => P x out ∧ x ∉ free) (claims l b.1) := by
    ext x
    simp [events]
  rw [success_eq_branch l v P, success_eq_branch l v (fun x out => P x out ∧ x ∉ free)]
  simpa only [he] using Noise.success_le_sdiff_add amp events free (branch_mass_le_one l v hv)

/-- Theorem 3.5(a) with coefficient one, for the measured query model. -/
theorem measured_success_le_noise_with_free [Nonempty G] [DecidableEq G]
    (l : List (Step W (Fin n) G O)) (v : State W) (hv : ‖v‖ ^ 2 ≤ 1)
    (P : (Fin n → G) → List O → Prop) (free : Finset (Fin n → G)) (A : Finset (Fin n)) {p β : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hβ : 0 ≤ β)
    (hrow : ∀ out x, P x out → x ∉ free →
      ∑ y ∈ eventInputs (fun y out => P y out ∧ y ∉ free) out, Noise.kernel A p x y ≤ β) :
    success l v P ≤ ((1 - p) ^ queries l)⁻¹ * β +
      (Fintype.card (Fin n → G) : ℝ)⁻¹ * free.card :=
  (success_le_remove_inputs l v hv P free).trans (add_le_add_left
    (measured_success_le_noise l v hv _ A hp0 hp1 hβ (fun out x h => hrow out x h.1 h.2)) _)

end QuantumNoiseStability.TimeSpace
end
end

-- Solutions.SortingRankGaps
section
/-! Gap counts for the stable ranks in the mission's sorting function. -/

set_option autoImplicit false

namespace QNoiseStab.Supplement

open Finset

variable {n m Δ d : ℕ}

/-- Every claimed value and rank agrees with the sorting output at that index. -/
def CorrectOn (τ : Fin n → Option (Fin m × Fin n)) (x : Fin n → Fin m) : Prop :=
  ∀ i a, τ i = some a → sortFun x i = a

instance (τ : Fin n → Option (Fin m × Fin n)) (x : Fin n → Fin m) :
    Decidable (CorrectOn τ x) := inferInstanceAs (Decidable (∀ i a, τ i = some a → sortFun x i = a))

/-- The input indices for which the partial output makes a claim. -/
def claimDomain (τ : Fin n → Option (Fin m × Fin n)) : Finset (Fin n) :=
  univ.filter fun i => (τ i).isSome

/-- Distinct indices in the witness set have claimed values at distance greater than m / Δ. -/
def SpacedOn (τ : Fin n → Option (Fin m × Fin n)) (I : Finset (Fin n)) (Δ : ℕ) : Prop :=
  ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ a b, τ i = some a → τ j = some b →
    m < Δ * Nat.dist a.1.val b.1.val

private abbrev Key (m n : ℕ) := Fin m ×ₗ Fin n

private def below (x : Fin n → Fin m) (a : Key m n) : Finset (Fin n) :=
  univ.filter fun i => toLex (x i, i) < a

private theorem card_below_claim {τ : Fin n → Option (Fin m × Fin n)} {x : Fin n → Fin m}
    (hx : CorrectOn τ x) {i : Fin n} {v : Fin m} {r : Fin n} (h : τ i = some (v, r)) :
    (below x (toLex (v, i))).card = r.val := by
  have he := hx i _ h
  have hv : x i = v := congrArg Prod.fst he
  rw [← hv]
  simpa only [below, sortFun, Prod.Lex.toLex_lt_toLex] using congrArg (fun a => a.2.val) he

private def gap (a : Fin (d + 2) → Key m n) (j : Fin (d + 1)) (i : Fin n) (v : Fin m) : Prop :=
  a j.castSucc ≤ toLex (v, i) ∧ toLex (v, i) < a j.succ

private theorem gap_unique {a : Fin (d + 2) → Key m n} (ha : Monotone a)
    {j k : Fin (d + 1)} {i : Fin n} {v : Fin m} (hj : gap a j i v) (hk : gap a k i v) :
    j = k := by
  have ordered {p q : Fin (d + 1)} (h : p < q) : a p.succ ≤ a q.castSucc :=
    ha (show p.val + 1 ≤ q.val from h)
  rcases lt_trichotomy j k with h | h | h
  · exact (hj.2.not_ge ((ordered h).trans hk.1)).elim
  · exact h
  · exact (hk.2.not_ge ((ordered h).trans hj.1)).elim

open scoped Classical in
private noncomputable def category (a : Fin (d + 2) → Key m n) (i : Fin n) (v : Fin m) :
    Fin (d + 1) :=
  if h : ∃ j : Fin d, gap a j.castSucc i v then h.choose.castSucc else Fin.last d

private theorem category_eq_castSucc {a : Fin (d + 2) → Key m n} (ha : Monotone a)
    (j : Fin d) (i : Fin n) (v : Fin m) :
    category a i v = j.castSucc ↔ gap a j.castSucc i v := by
  unfold category
  split
  next h =>
    exact ⟨fun e => e ▸ h.choose_spec, fun hj => gap_unique ha h.choose_spec hj⟩
  next h => exact iff_of_false (Fin.castSucc_lt_last j).ne' (fun hj => h ⟨j, hj⟩)

private theorem category_of_gap {a : Fin (d + 2) → Key m n} (ha : Monotone a)
    {j : Fin (d + 1)} {i : Fin n} {v : Fin m} (h : gap a j i v) : category a i v = j := by
  induction j using Fin.lastCases with
  | cast j => exact (category_eq_castSucc ha j i v).2 h
  | last =>
    have hnone : ¬ ∃ k : Fin d, gap a k.castSucc i v := fun ⟨k, hk⟩ =>
      (Fin.castSucc_lt_last k).ne (gap_unique ha hk h)
    simp [category, hnone]

open scoped Classical in
private theorem card_gap (a : Fin (d + 2) → Key m n) (ha : Monotone a)
    (x : Fin n → Fin m) (j : Fin (d + 1)) :
    (univ.filter fun i => gap a j i (x i)).card =
      (below x (a j.succ)).card - (below x (a j.castSucc)).card := by
  classical
  have h : (univ.filter fun i => gap a j i (x i)) =
      below x (a j.succ) \ below x (a j.castSucc) := by
    ext i
    constructor
    · intro hi
      obtain ⟨hlo, hhi⟩ := (mem_filter.mp hi).2
      exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _, hhi⟩, fun hlo' =>
        hlo.not_gt (mem_filter.mp hlo').2⟩
    · intro hi
      obtain ⟨hhi, hlo⟩ := mem_sdiff.mp hi
      exact mem_filter.mpr ⟨mem_univ _, le_of_not_gt (fun h => hlo (mem_filter.mpr ⟨mem_univ _, h⟩)),
        (mem_filter.mp hhi).2⟩
  rw [h, card_sdiff_of_subset]
  intro i hi
  exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2.trans_le (ha Fin.castSucc_lt_succ.le)⟩

/-- With d + 2 spaced claims, every correct input has the same counts in d + 1
categories. At each coordinate, each category contains at least 15m / (16Δ) letters. -/
theorem exists_gapCategories_of_widelySpaced {τ : Fin n → Option (Fin m × Fin n)}
    {x : Fin n → Fin m} (hx : CorrectOn τ x) {I : Finset (Fin n)} (hI : I ⊆ claimDomain τ)
    (hcard : I.card = d + 2) (hsep : SpacedOn τ I Δ) (hm : 16 * Δ ≤ m) :
    ∃ c : Fin n → Fin m → Fin (d + 1),
      (∀ i j, 15 * m ≤ 16 * Δ * (univ.filter fun v => c i v = j).card) ∧
      ∀ y, CorrectOn τ y → ∀ j, (univ.filter fun i => c i (x i) = j).card =
        (univ.filter fun i => c i (y i) = j).card := by
  classical
  have claim {i} (hi : i ∈ I) : τ i = some (sortFun x i) := by
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (mem_filter.mp (hI hi)).2
    rwa [hx i a ha]
  have sep {i j} (hi : i ∈ I) (hj : j ∈ I) (hne : i ≠ j) :
      m < Δ * Nat.dist (x i).val (x j).val :=
    hsep i hi j hj hne _ _ (claim hi) (claim hj)
  have hinj : Set.InjOn x I := by
    intro i hi j hj he
    by_contra hne
    simpa [he] using sep hi hj hne
  let values := (I.image x).orderEmbOfFin ((card_image_of_injOn hinj).trans hcard)
  have preimage (j : Fin (d + 2)) : ∃ i ∈ I, x i = values j :=
    mem_image.mp ((I.image x).orderEmbOfFin_mem _ j)
  choose idx hidx hval using preimage
  let a (j : Fin (d + 2)) : Key m n := toLex (values j, idx j)
  have ha : Monotone a := (show StrictMono a from fun _ _ h =>
    Prod.Lex.toLex_lt_toLex.mpr (Or.inl (values.strictMono h))).monotone
  refine ⟨category a, ?_, ?_⟩
  · intro i j
    have hv := values.strictMono (show j.castSucc < j.succ from Fin.castSucc_lt_succ)
    have hne : idx j.castSucc ≠ idx j.succ := by
      intro he
      exact hv.ne ((hval _).symm.trans ((congrArg x he).trans (hval _)))
    have hs := sep (hidx _) (hidx _) hne
    simp only [hval, Nat.dist_eq_sub_of_le (show (values j.castSucc).val ≤ _ from hv.le)] at hs
    have hsub : Ioo (values j.castSucc) (values j.succ) ⊆
        univ.filter fun v => category a i v = j := by
      intro v hv'
      obtain ⟨h₁, h₂⟩ := mem_Ioo.mp hv'
      exact mem_filter.mpr ⟨mem_univ _, category_of_gap ha
        ⟨Prod.Lex.toLex_le_toLex.mpr (Or.inl h₁), Prod.Lex.toLex_lt_toLex.mpr (Or.inl h₂)⟩⟩
    have hc := card_le_card hsub
    rw [Fin.card_Ioo] at hc
    have h := Nat.mul_le_mul_left Δ (show (values j.succ).val - (values j.castSucc).val ≤
        (univ.filter fun v => category a i v = j).card + 1 by omega)
    rw [Nat.mul_add, Nat.mul_one] at h
    rw [Nat.mul_assoc]
    omega
  · intro y hy j
    have hbelow (k : Fin (d + 2)) : (below x (a k)).card = (below y (a k)).card := by
      have h : τ (idx k) = some (values k, (sortFun x (idx k)).2) := by
        rw [← hval k]
        exact claim (hidx k)
      exact (card_below_claim hx h).trans (card_below_claim hy h).symm
    have hgap (k : Fin d) :
        (univ.filter fun i => category a i (x i) = k.castSucc).card =
        (univ.filter fun i => category a i (y i) = k.castSucc).card := by
      simp only [category_eq_castSucc ha, card_gap a ha, hbelow]
    induction j using Fin.lastCases with
    | cast k => exact hgap k
    | last =>
      have total (z : Fin n → Fin m) :
          (∑ k : Fin d, (univ.filter fun i => category a i (z i) = k.castSucc).card) +
          (univ.filter fun i => category a i (z i) = Fin.last d).card = n := by
        simpa [Fin.sum_univ_castSucc] using
          sum_card_fiberwise_eq_card_filter univ univ (fun i => category a i (z i))
      simpa only [hgap, Nat.add_right_inj] using (total x).trans (total y).symm

end QNoiseStab.Supplement
end

-- Solutions.SortingProbability
section
/-!
# Atoms of sums of independent Bernoulli variables

Appendix A, Proposition A.1 of arXiv:2609.40334v3, with absolute constant
`√(π / 8)`. Fourier inversion on `[-1, 1]` expresses each atom as an integral.
The squared norm of one Bernoulli factor at angle `θ` is
`1 - 2 * p * (1 - p) * (1 - cos θ)`, giving a Gaussian upper bound.
-/


namespace QuantumNoiseStability.Probability

open Finset Real MeasureTheory
open scoped BigOperators

variable {n : ℕ}

/-- Probability of one bit assignment under the independent Bernoulli product law. -/
noncomputable def bernoulliWeight (p : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  ∏ i, if x i then p i else 1 - p i

/-- Number of successes in a bit assignment. -/
def bernoulliCount (x : Fin n → Bool) : ℕ := ∑ i, if x i then 1 else 0

/-- Probability that the number of successes is exactly `k`. -/
noncomputable def bernoulliAtom (p : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ x ∈ univ.filter (fun x => bernoulliCount x = k), bernoulliWeight p x

/-- Variance of the sum under the product law. -/
noncomputable def bernoulliVariance (p : Fin n → ℝ) : ℝ := ∑ i, p i * (1 - p i)

theorem bernoulliWeight_nonneg {p : Fin n → ℝ} (h₀ : ∀ i, 0 ≤ p i)
    (h₁ : ∀ i, p i ≤ 1) (x : Fin n → Bool) : 0 ≤ bernoulliWeight p x :=
  prod_nonneg fun i _ => by
    split
    · exact h₀ i
    · exact sub_nonneg.mpr (h₁ i)

theorem sum_bernoulliWeight (p : Fin n → ℝ) : ∑ x, bernoulliWeight p x = 1 := by
  classical
  unfold bernoulliWeight
  rw [← Fintype.prod_sum (fun i (b : Bool) => if b then p i else 1 - p i)]
  simp

theorem bernoulliAtom_nonneg {p : Fin n → ℝ} (h₀ : ∀ i, 0 ≤ p i)
    (h₁ : ∀ i, p i ≤ 1) (k : ℕ) : 0 ≤ bernoulliAtom p k :=
  sum_nonneg fun x _ => bernoulliWeight_nonneg h₀ h₁ x

private noncomputable def phase (m : ℤ) (t : ℝ) : ℂ :=
  Complex.exp ((↑((m : ℝ) * π * t) : ℂ) * Complex.I)

private theorem integral_phase (m : ℤ) :
    (∫ t in (-1 : ℝ)..1, phase m t) = if m = 0 then 2 else 0 := by
  by_cases hm : m = 0
  · subst m
    norm_num [phase, intervalIntegral.integral_const, Complex.real_smul]
  rw [if_neg hm]
  let c : ℂ := (m : ℂ) * π * Complex.I
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast hm)
      (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have he (t : ℝ) : phase m t = Complex.exp (c * t) := by
    unfold phase c
    push_cast
    ring_nf
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  simp only [Complex.ofReal_one, Complex.ofReal_neg, mul_one, mul_neg]
  have h : Complex.exp c = Complex.exp (-c) := by
    dsimp [c]
    rw [← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg,
      Complex.sin_neg, Complex.sin_int_mul_pi]
    simp
  rw [h, sub_self, zero_div]

/-- Evaluation of the probability generating polynomial by expanding the product. -/
private theorem generating_product (p : Fin n → ℝ) (z : ℂ) :
    ∏ i, (↑(1 - p i) + (p i : ℂ) * z) =
      ∑ x, (bernoulliWeight p x : ℂ) * z ^ bernoulliCount x := by
  classical
  let f (i : Fin n) (b : Bool) : ℂ :=
    (↑(if b then p i else 1 - p i) : ℂ) * z ^ (if b then 1 else 0 : ℕ)
  calc
    _ = ∏ i, ∑ b, f i b := by simp [f, add_comm]
    _ = _ := by
      rw [Fintype.prod_sum]
      apply sum_congr rfl
      intro x _
      simp only [f, prod_mul_distrib, prod_pow_eq_pow_sum, bernoulliCount, bernoulliWeight,
        Complex.ofReal_prod]

private noncomputable def integrand (p : Fin n → ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  phase (-(k : ℤ)) t * ∏ i, (↑(1 - p i) + (p i : ℂ) * phase 1 t)

private theorem integral_integrand (p : Fin n → ℝ) (k : ℕ) :
    (∫ t in (-1 : ℝ)..1, integrand p k t) = 2 * (bernoulliAtom p k : ℂ) := by
  classical
  have shift (j : ℕ) (t : ℝ) :
      phase (-(k : ℤ)) t * phase 1 t ^ j = phase ((j : ℤ) - k) t := by
    unfold phase
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have expand (t : ℝ) : integrand p k t =
      ∑ x, (bernoulliWeight p x : ℂ) * phase ((bernoulliCount x : ℤ) - k) t := by
    unfold integrand
    rw [generating_product, mul_sum]
    exact sum_congr rfl fun x _ => by rw [mul_left_comm, shift]
  simp_rw [expand]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul, integral_phase]
    simp only [bernoulliAtom, Complex.ofReal_sum, sum_filter, mul_sum]
    apply sum_congr rfl
    intro x _
    by_cases h : bernoulliCount x = k
    · simp [h, mul_comm]
    · have h' : (bernoulliCount x : ℤ) - k ≠ 0 := by omega
      simp [h, h']
  · intro x _
    apply Continuous.intervalIntegrable
    unfold phase
    fun_prop

private theorem factor_bound {p t : ℝ} (h₀ : 0 ≤ p) (h₁ : p ≤ 1) (ht : |t| ≤ 1) :
    ‖(↑(1 - p) : ℂ) + (p : ℂ) * phase 1 t‖ ≤ exp (-2 * (p * (1 - p)) * t ^ 2) := by
  have hz : ‖phase 1 t‖ = 1 := by
    simpa only [phase, Int.cast_one, one_mul] using Complex.norm_exp_ofReal_mul_I (π * t)
  have hre : (phase 1 t).re = cos (π * t) := by
    simpa only [phase, Int.cast_one, one_mul] using Complex.exp_ofReal_mul_I_re (π * t)
  have hsq : ‖(↑(1 - p) : ℂ) + (p : ℂ) * phase 1 t‖ ^ 2 =
      1 - 2 * (p * (1 - p)) * (1 - cos (π * t)) := by
    rw [Complex.sq_norm, Complex.normSq_add, Complex.normSq_mul,
      ← Complex.sq_norm (phase 1 t), hz]
    rw [Complex.normSq_ofReal]
    simp [Complex.mul_re, hre]
    ring
  have hπ : |π * t| ≤ π := by
    rw [abs_mul, abs_of_pos pi_pos]
    simpa using mul_le_mul_of_nonneg_left ht pi_pos.le
  have hc := Real.cos_le_one_sub_mul_cos_sq hπ
  have hs : 2 / π ^ 2 * (π * t) ^ 2 = 2 * t ^ 2 := by field_simp
  rw [hs] at hc
  have hv : 0 ≤ 2 * (p * (1 - p)) := by positivity [sub_nonneg.mpr h₁]
  apply le_of_sq_le_sq _ (exp_pos _).le
  rw [hsq, sq, ← Real.exp_add]
  have hd := mul_le_mul_of_nonneg_left (show 2 * t ^ 2 ≤ 1 - cos (π * t) by linarith) hv
  linarith [Real.add_one_le_exp (-2 * (p * (1 - p)) * t ^ 2 + -2 * (p * (1 - p)) * t ^ 2)]

private theorem integrand_bound {p : Fin n → ℝ} (h₀ : ∀ i, 0 ≤ p i)
    (h₁ : ∀ i, p i ≤ 1) (k : ℕ) {t : ℝ} (ht : |t| ≤ 1) :
    ‖integrand p k t‖ ≤ exp (-(2 * bernoulliVariance p) * t ^ 2) := by
  have hphase : ‖phase (-(k : ℤ)) t‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  rw [integrand, norm_mul, hphase, one_mul, norm_prod]
  calc
    _ ≤ ∏ i, exp (-2 * (p i * (1 - p i)) * t ^ 2) :=
      prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => factor_bound (h₀ i) (h₁ i) ht
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp only [bernoulliVariance, ← sum_mul, ← mul_sum]
      ring

/-- Proposition A.1 with absolute constant `√(π / 8)`, including zero variance. -/
theorem sqrt_variance_mul_bernoulliAtom_le {p : Fin n → ℝ} (h₀ : ∀ i, 0 ≤ p i)
    (h₁ : ∀ i, p i ≤ 1) (k : ℕ) :
    √(bernoulliVariance p) * bernoulliAtom p k ≤ √(π / 8) := by
  have hv : 0 ≤ bernoulliVariance p :=
    sum_nonneg fun i _ => mul_nonneg (h₀ i) (sub_nonneg.mpr (h₁ i))
  rcases hv.eq_or_lt with h | h
  · rw [← h, Real.sqrt_zero, zero_mul]
    exact sqrt_nonneg _
  have hab : (-1 : ℝ) ≤ 1 := by norm_num
  have hnorm : ‖∫ t in (-1 : ℝ)..1, integrand p k t‖ = 2 * bernoulliAtom p k := by
    rw [integral_integrand, norm_mul, Complex.norm_real, Real.norm_of_nonneg
      (bernoulliAtom_nonneg h₀ h₁ k)]
    norm_num
  have hbound : 2 * bernoulliAtom p k ≤ √(π / (2 * bernoulliVariance p)) := calc
    _ = _ := hnorm.symm
    _ ≤ ∫ t in (-1 : ℝ)..1, ‖integrand p k t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ t in (-1 : ℝ)..1, exp (-(2 * bernoulliVariance p) * t ^ 2) := by
      apply intervalIntegral.integral_mono_on hab
      · apply Continuous.intervalIntegrable
        unfold integrand phase
        fun_prop
      · apply Continuous.intervalIntegrable
        fun_prop
      · exact fun t ht => integrand_bound h₀ h₁ k (abs_le.mpr ht)
    _ ≤ ∫ t : ℝ, exp (-(2 * bernoulliVariance p) * t ^ 2) := by
      rw [intervalIntegral.integral_of_le hab]
      exact setIntegral_le_integral (integrable_exp_neg_mul_sq (by positivity))
        (ae_of_all _ fun _ => (exp_pos _).le)
    _ = _ := integral_gaussian _
  have hm := mul_le_mul_of_nonneg_left hbound (sqrt_nonneg (bernoulliVariance p))
  rw [← Real.sqrt_mul hv] at hm
  have hr : bernoulliVariance p * (π / (2 * bernoulliVariance p)) = (π / 8) * 2 ^ 2 := by
    field_simp
    ring
  rw [hr, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at hm
  linarith

/-- If every success and failure probability is at least `γ`, each count has
probability at most `1 / √(γ * n)`. -/
theorem bernoulliAtom_le_of_uniform {p : Fin n → ℝ} {γ : ℝ} (hγ : 0 < γ) (hn : 0 < n)
    (hlo : ∀ i, γ ≤ p i) (hhi : ∀ i, p i ≤ 1 - γ) (k : ℕ) :
    bernoulliAtom p k ≤ 1 / √(γ * n) := by
  have h₀ i := hγ.le.trans (hlo i)
  have h₁ i : p i ≤ 1 := by linarith [hhi i]
  have hv : γ * n / 2 ≤ bernoulliVariance p := calc
    _ = ∑ _ : Fin n, γ / 2 := by simp; ring
    _ ≤ _ := by
      apply sum_le_sum
      intro i _
      rcases le_total (p i) (1 / 2) with hi | hi
      · nlinarith [mul_nonneg (h₀ i) (show 0 ≤ 1 / 2 - p i by linarith), hlo i]
      · nlinarith [mul_nonneg (sub_nonneg.mpr (h₁ i)) (show 0 ≤ p i - 1 / 2 by linarith), hhi i]
  have hs : √(γ * n) ≤ √2 * √(bernoulliVariance p) := by
    rw [← sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact sqrt_le_sqrt (by linarith)
  apply (le_div_iff₀ (Real.sqrt_pos.2 (by positivity))).2
  calc
    _ = √(γ * n) * bernoulliAtom p k := mul_comm _ _
    _ ≤ (√2 * √(bernoulliVariance p)) * bernoulliAtom p k :=
      mul_le_mul_of_nonneg_right hs (bernoulliAtom_nonneg h₀ h₁ k)
    _ ≤ √2 * √(π / 8) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (sqrt_variance_mul_bernoulliAtom_le h₀ h₁ k) (sqrt_nonneg _)
    _ ≤ 1 := by
      rw [← sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_le_iff]
      constructor <;> linarith [Real.pi_le_four]

end QuantumNoiseStability.Probability

/-!
# Point probabilities for independent categorical trials

Appendix A of Beame, Holman and Kornerup (arXiv:2609.40334v3), Proposition 5.21.
We condition on the positions occupied by a category of minimum target count.
-/

namespace QuantumNoiseStability.Probability

open Finset
open scoped Classical
noncomputable section

variable {ι α : Type} [Fintype ι] [Fintype α]

/-- Number of occurrences of a category in an assignment. -/
def categoricalCount [DecidableEq α] (x : ι → α) (a : α) : ℕ :=
  ∑ i, if x i = a then 1 else 0

/-- Mass at a histogram under independent rows of categorical probabilities. -/
def categoricalAtom (P : ι → α → ℝ) (c : α → ℕ) : ℝ := by
  classical
  exact ∑ x : ι → α, if categoricalCount x = c then ∏ i, P i (x i) else 0

/-- The one-dimensional input, with a common lower bound for both outcomes.
The constant is independent of the number of trials and of their probabilities. -/
def BernoulliAtomBound (B : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ (p : Fin n → ℝ) (γ : ℝ), 0 < γ →
    (∀ i, γ ≤ p i) → (∀ i, γ ≤ 1 - p i) → ∀ t : ℕ,
    (∑ b : Fin n → Bool, if categoricalCount b true = t then
      ∏ i, (if b i then p i else 1 - p i) else 0) ≤ B / Real.sqrt (γ * n)

private def hits [DecidableEq α] (a : α) (x : ι → α) : ι → Bool :=
  fun i => decide (x i = a)

private abbrev Miss (b : ι → Bool) := {i // b i ≠ true}
private abbrev Other (a : α) := {v // v ≠ a}

private def assemble (a : α) (b : ι → Bool) (y : Miss b → Other a) (i : ι) : α :=
  if h : b i = true then a else (y ⟨i, h⟩).val

private def splitEquiv [DecidableEq α] (a : α) (b : ι → Bool) :
    (Miss b → Other a) ≃ {x : ι → α // hits a x = b} where
  toFun y := ⟨assemble a b y, by
    funext i
    by_cases h : b i = true
    · simp [assemble, hits, h]
    · simp [assemble, hits, h, (y ⟨i, h⟩).property]⟩
  invFun x i := ⟨x.val i, by
    intro h
    have hb := congrFun x.property i.val
    exact i.property (by simpa [hits, h] using hb.symm)⟩
  left_inv y := by funext i; apply Subtype.ext; simp [assemble, i.property]
  right_inv x := by
    apply Subtype.ext
    funext i
    by_cases h : b i = true
    · have hx : x.val i = a := by simpa [hits, h] using congrFun x.property i
      simp [assemble, h, hx]
    · simp [assemble, h]

omit [Fintype α] in
private theorem count_assemble [DecidableEq α] (a : α) (b : ι → Bool)
    (y : Miss b → Other a) (c : α → ℕ) :
    categoricalCount (assemble a b y) = c ↔
      categoricalCount b true = c a ∧ categoricalCount y = fun v => c v.val := by
  classical
  have ha : categoricalCount (assemble a b y) a = categoricalCount b true := by
    apply sum_congr rfl
    intro i _
    by_cases h : b i = true <;> simp [assemble, h, (y _).property]
  have hv (v : Other a) : categoricalCount (assemble a b y) v.val = categoricalCount y v := by
    unfold categoricalCount
    rw [← Fintype.sum_subtype_add_sum_subtype (fun i => b i = true)]
    rw [sum_eq_zero (fun i _ => by simp [assemble, i.property, Ne.symm v.property]), zero_add]
    apply sum_congr rfl
    intro i _
    simp [assemble, i.property, Subtype.ext_iff]
  constructor
  · intro h
    exact ⟨ha ▸ congrFun h a, funext fun v => hv v ▸ congrFun h v.val⟩
  · rintro ⟨h, hy⟩
    funext j
    by_cases hj : j = a
    · simpa [hj, ha] using h
    · exact (hv ⟨j, hj⟩).trans (congrFun hy ⟨j, hj⟩)

omit [Fintype α] in
private theorem mass_assemble (P : ι → α → ℝ) (a : α) (b : ι → Bool)
    (y : Miss b → Other a) (hp : ∀ i, 1 - P i a ≠ 0) :
    (∏ i, P i (assemble a b y i)) =
      (∏ i, if b i then P i a else 1 - P i a) *
      ∏ i : Miss b, P i (y i) / (1 - P i a) := by
  classical
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => b i = true)
    (fun i => P i (assemble a b y i)),
    ← Fintype.prod_subtype_mul_prod_subtype (fun i => b i = true)
      (fun i => if b i then P i a else 1 - P i a), mul_assoc, ← prod_mul_distrib]
  congr 1
  · apply prod_congr rfl
    intro i _
    simp [assemble, i.property]
  · apply prod_congr rfl
    intro i _
    simp [assemble, i.property, mul_comm (1 - P _ a), hp]

/-- Exact decomposition by the Boolean assignment marking all occurrences of `a`. -/
theorem categoricalAtom_condition (P : ι → α → ℝ) (a : α) (c : α → ℕ)
    (hp : ∀ i, 1 - P i a ≠ 0) :
    categoricalAtom P c = ∑ b : ι → Bool, if categoricalCount b true = c a then
      (∏ i, if b i then P i a else 1 - P i a) *
        categoricalAtom (fun (i : {i // b i ≠ true}) (v : {v // v ≠ a}) => P i v / (1 - P i a))
          (fun v => c v.val) else 0 := by
  classical
  unfold categoricalAtom
  let e := (Equiv.sigmaCongrRight (splitEquiv (ι := ι) a)).trans (Equiv.sigmaFiberEquiv (hits a))
  let g (x : ι → α) := if categoricalCount x = c then ∏ i, P i (x i) else 0
  refine (e.sum_comp g).symm.trans ?_
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro b _
  change (∑ y : Miss b → Other a,
    if categoricalCount (assemble a b y) = c then ∏ i, P i (assemble a b y i) else 0) = _
  by_cases hb : categoricalCount b true = c a
  · simp only [count_assemble, hb, true_and, ite_true, mul_sum]
    apply sum_congr (by ext; simp)
    intro y _
    rw [mass_assemble P a b y hp, mul_ite, mul_zero]
    congr 1
    congr!
  · simp [count_assemble, hb]

private theorem bernoulli_bound_fintype [DecidableEq ι] {B γ : ℝ} (hB : BernoulliAtomBound B)
    (hn : 0 < Fintype.card ι) (p : ι → ℝ) (hγ : 0 < γ)
    (h₀ : ∀ i, γ ≤ p i) (h₁ : ∀ i, γ ≤ 1 - p i) (t : ℕ) :
    (∑ b : ι → Bool, if categoricalCount b true = t then
      ∏ i, (if b i then p i else 1 - p i) else 0) ≤ B / Real.sqrt (γ * Fintype.card ι) := by
  classical
  let e := (Fintype.equivFin ι).symm
  let f := e.arrowCongr (Equiv.refl Bool)
  have h := hB _ hn (fun j => p (e j)) γ hγ (fun j => h₀ _) (fun j => h₁ _) t
  apply le_trans (le_of_eq _) h
  rw [← f.sum_comp]
  apply sum_congr rfl
  intro b _
  have hc : categoricalCount (f b) true = categoricalCount b true := by
    unfold categoricalCount
    rw [← e.sum_comp]
    simp [f]
  rw [hc]
  congr 1
  rw [← e.prod_comp]
  simp [f]

theorem categoricalAtom_le_one (P : ι → α → ℝ) (h₀ : ∀ i v, 0 ≤ P i v)
    (hs : ∀ i, ∑ v, P i v = 1) (c : α → ℕ) : categoricalAtom P c ≤ 1 := by
  classical
  calc
    categoricalAtom P c ≤ ∑ x : ι → α, ∏ i, P i (x i) := by
      apply sum_le_sum
      intro x _
      split_ifs <;> simp [prod_nonneg fun i _ => h₀ i (x i)]
    _ = 1 := by rw [← Fintype.prod_sum P]; simp [hs]

theorem sum_categoricalCount [DecidableEq α] (x : ι → α) :
    ∑ v, categoricalCount x v = Fintype.card ι := by
  classical
  unfold categoricalCount
  rw [sum_comm]
  simp

theorem categoricalAtom_eq_zero_of_sum_ne (P : ι → α → ℝ) (c : α → ℕ)
    (hc : ∑ v, c v ≠ Fintype.card ι) : categoricalAtom P c = 0 := by
  classical
  apply sum_eq_zero
  intro x _
  by_cases h : categoricalCount x = c
  · exact (hc (h ▸ sum_categoricalCount x)).elim
  · simp [h]

/-- With zero trials the zero histogram has all the mass. -/
theorem categoricalAtom_zero_trials (P : Fin 0 → α → ℝ) (c : α → ℕ) :
    categoricalAtom P c = if c = 0 then 1 else 0 := by
  classical
  have hc (x : Fin 0 → α) : categoricalCount x = 0 := by
    funext v
    simp [categoricalCount]
  simp [categoricalAtom, hc, eq_comm]

/-- Losing at most the average target count in one conditioning step costs
at most a factor of `√e` in the induction. -/
private theorem conditioning_step {n m γ B : ℝ} (k : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hγ : 0 < γ) (hB : 0 ≤ B) (hsize : n * (k + 1) ≤ m * (k + 2)) :
    B / Real.sqrt (γ * n) * (B * Real.sqrt (Real.exp 1) / Real.sqrt (γ * m)) ^ k ≤
      (B * Real.sqrt (Real.exp 1) / Real.sqrt (γ * n)) ^ (k + 1) := by
  let q := 1 + ((k : ℝ) + 1)⁻¹
  have hq : 1 ≤ q := by dsimp [q]; linarith [show 0 < ((k : ℝ) + 1)⁻¹ by positivity]
  have hqm : n ≤ m * q := by
    dsimp [q]
    have hk : 0 < (k : ℝ) + 1 := by positivity
    rw [mul_add, mul_one, ← div_eq_mul_inv]
    apply (sub_le_iff_le_add').mp
    apply (le_div_iff₀ hk).mpr
    linarith only [hsize]
  have hpow : q ^ k ≤ Real.exp 1 := calc
    q ^ k ≤ q ^ (k + 1) := pow_le_pow_right₀ hq (by omega)
    _ ≤ Real.exp 1 := by simpa [q] using (Real.one_add_inv_pow_le_exp (n := k + 1))
  have hroot : (Real.sqrt q) ^ k ≤ Real.sqrt (Real.exp 1) := by
    apply Real.le_sqrt_of_sq_le
    rwa [← pow_mul, Nat.mul_comm, pow_mul, Real.sq_sqrt (by linarith)]
  let K := B * Real.sqrt (Real.exp 1)
  have hscale : K / Real.sqrt (γ * m) ≤ K / Real.sqrt (γ * n) * Real.sqrt q := by
    have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hqm hγ.le)
    rw [← mul_assoc, Real.sqrt_mul (by positivity : 0 ≤ γ * m)] at hs
    have hsn : 0 < Real.sqrt (γ * n) := by positivity
    have hsm : 0 < Real.sqrt (γ * m) := by positivity
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hsm hsn]
    calc K * Real.sqrt (γ * n) ≤ K * (Real.sqrt (γ * m) * Real.sqrt q) :=
           mul_le_mul_of_nonneg_left hs (by dsimp [K]; positivity)
         _ = _ := by ring
  change B / _ * (K / _) ^ k ≤ (K / _) ^ (k + 1)
  calc
    _ ≤ B / Real.sqrt (γ * n) * (K / Real.sqrt (γ * n) * Real.sqrt q) ^ k := by
      gcongr
    _ = (K / Real.sqrt (γ * n)) ^ k * (B / Real.sqrt (γ * n) * Real.sqrt q ^ k) := by
      rw [mul_pow]; ring
    _ ≤ (K / Real.sqrt (γ * n)) ^ k * (B / Real.sqrt (γ * n) * Real.sqrt (Real.exp 1)) := by
      gcongr
    _ = _ := by rw [pow_succ]; dsimp [K]; ring

private theorem categorical_bound_aux {B γ : ℝ} (hB : BernoulliAtomBound B)
    (hB₀ : 0 ≤ B) (hγ : 0 < γ) (k : ℕ) :
    ∀ {ι α : Type} [Fintype ι] [Fintype α], Fintype.card α = k + 1 →
    0 < Fintype.card ι → ∀ (P : ι → α → ℝ), (∀ i, ∑ v, P i v = 1) →
    (∀ i v, γ ≤ P i v) → ∀ c : α → ℕ, categoricalAtom P c ≤
      (B * Real.sqrt (Real.exp 1) / Real.sqrt (γ * Fintype.card ι)) ^ k := by
  classical
  induction k with
  | zero =>
    intro ι α _ _ _ _ P hs hP c
    simpa using categoricalAtom_le_one P (fun i v => hγ.le.trans (hP i v)) hs c
  | succ k ih =>
    intro ι α _ _ hd hn P hs hP c
    by_cases hsum : ∑ v, c v = Fintype.card ι
    case neg => rw [categoricalAtom_eq_zero_of_sum_ne _ _ hsum]; positivity
    have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨a, ha⟩ := Finite.exists_min c
    have hcard : Fintype.card (Other a) = k + 1 := by
      simp [Other, Fintype.card_subtype_compl, hd]
    have : Nonempty (Other a) := Fintype.card_pos_iff.mp (by omega)
    have htail (i : ι) : ∑ v : Other a, P i v = 1 - P i a := by
      rw [← Finset.sum_subtype (univ.erase a) (fun j => by simp) (P i)]
      exact eq_sub_of_add_eq ((sum_erase_add _ _ (mem_univ a)).trans (hs i))
    have hfail (i : ι) : γ ≤ 1 - P i a := by
      let v : Other a := Classical.choice inferInstance
      rw [← htail]
      exact (hP i v).trans
        (single_le_sum (fun (j : Other a) _ => hγ.le.trans (hP i j)) (mem_univ v))
    have hpos (i : ι) := hγ.trans_le (hfail i)
    have hmin : (k + 2) * c a ≤ Fintype.card ι := by
      have h := sum_le_sum (s := univ) (fun j _ => ha j)
      simpa [hsum, hd] using h
    let m := Fintype.card ι - c a
    have hca : c a ≤ Fintype.card ι := by
      exact (Nat.le_mul_of_pos_left _ (by omega : 0 < k + 2)).trans hmin
    have hsize : Fintype.card ι * (k + 1) ≤ m * (k + 2) := by
      dsimp [m]
      rw [Nat.sub_mul, Nat.le_sub_iff_add_le (by gcongr)]
      nlinarith only [hmin]
    have hm : 0 < m := by
      by_contra! h
      have hz : m = 0 := by omega
      simp [hz, hn.ne'] at hsize
    let R := B * Real.sqrt (Real.exp 1) / Real.sqrt (γ * m)
    have hR : 0 ≤ R := by dsimp [R]; positivity
    rw [categoricalAtom_condition P a c (fun i => (hpos i).ne')]
    calc
      _ ≤ ∑ b : ι → Bool, (if categoricalCount b true = c a then
            ∏ i, (if b i then P i a else 1 - P i a) else 0) * R ^ k := by
        apply sum_le_sum
        intro b _
        by_cases hb : categoricalCount b true = c a
        · simp only [hb, ite_true]
          apply mul_le_mul_of_nonneg_left
          · have hbcard : Fintype.card (Miss b) = m := by
              rw [Fintype.card_subtype_compl (fun i => b i = true)]
              simp [Fintype.card_subtype, m, ← hb, categoricalCount]
            have h := ih (ι := Miss b) (α := Other a) hcard (hbcard ▸ hm)
              (fun i v => P i v / (1 - P i a))
              (fun i => by rw [← sum_div, htail, div_self (hpos _).ne'])
              (fun i v => by
                apply (le_div_iff₀ (hpos _)).mpr
                calc γ * (1 - P i a) ≤ γ * 1 := by
                       gcongr; linarith [hP i a]
                     _ ≤ P i v := by simpa using hP i v)
              (fun v => c v.val)
            simpa only [hbcard, R] using h
          · apply prod_nonneg
            intro i _
            split <;> first | exact hγ.le.trans (hP i a) | exact (hpos i).le
        · simp [hb]
      _ ≤ B / Real.sqrt (γ * Fintype.card ι) * R ^ k := by
        rw [← sum_mul]
        exact mul_le_mul_of_nonneg_right
          (bernoulli_bound_fintype hB hn (fun i => P i a) hγ (fun i => hP i a) hfail (c a))
          (pow_nonneg hR _)
      _ ≤ _ := conditioning_step k (by exact_mod_cast hn) (by exact_mod_cast hm) hγ hB₀
                 (by exact_mod_cast hsize)

/-- Proposition 5.21 for all positive numbers of trials and categories, parametrized
by the independent Bernoulli atom bound. The constant is independent of `n,d,γ,P,c`. -/
theorem poissonMultinomial_atom_le_of_bernoulli {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {B γ : ℝ} (hB : BernoulliAtomBound B) (hB₀ : 0 ≤ B) (hγ : 0 < γ)
    (P : Fin n → Fin d → ℝ) (hs : ∀ i, ∑ v, P i v = 1) (hP : ∀ i v, γ ≤ P i v)
    (c : Fin d → ℕ) :
    categoricalAtom P c ≤ (B * Real.sqrt (Real.exp 1) / Real.sqrt (γ * n)) ^ (d - 1) := by
  simpa using categorical_bound_aux hB hB₀ hγ (d - 1) (ι := Fin n) (α := Fin d)
    (by simp; omega) (by simpa using hn) P hs hP c

theorem bernoulliAtomBound_one : BernoulliAtomBound 1 := by
  intro n hn p γ hγ hlo hhi t
  have hc (b : Fin n → Bool) : categoricalCount b true = bernoulliCount b := by
    apply sum_congr rfl
    intro i _
    cases b i <;> rfl
  simpa only [bernoulliAtom, bernoulliWeight, sum_filter, hc] using
    (bernoulliAtom_le_of_uniform hγ hn hlo (fun i => by linarith [hhi i]) t)

/-- Proposition 5.21 with the absolute constant `e` inside the real power. -/
theorem poissonMultinomial_atom_le {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {γ : ℝ} (hγ : 0 < γ) (P : Fin n → Fin d → ℝ)
    (hs : ∀ i, ∑ v, P i v = 1) (hP : ∀ i v, γ ≤ P i v) (c : Fin d → ℕ) :
    categoricalAtom P c ≤ (Real.exp 1 / (γ * n)) ^ (((d - 1 : ℕ) : ℝ) / 2) := by
  have h := poissonMultinomial_atom_le_of_bernoulli hn hd bernoulliAtomBound_one
    (by norm_num) hγ P hs hP c
  rw [one_mul, ← Real.sqrt_div (Real.exp_pos _).le, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at h
  convert h using 2
  ring

end
end QuantumNoiseStability.Probability
end

-- Solutions.SortingWide
section
/-! The classical noise return bound for widely spaced partial sorting outputs. -/

set_option autoImplicit false

namespace QNoiseStab.Supplement

open Finset QuantumNoiseStability.Probability

private theorem category_mass {ι V J : Type} [Fintype ι] [Fintype V] [Fintype J]
    [DecidableEq ι] [DecidableEq J] (w : ι → V → ℝ) (c : ι → V → J) (t : J → ℕ) :
    categoricalAtom (fun i j => ∑ v, if c i v = j then w i v else 0) t =
      ∑ y : ι → V, if categoricalCount (fun i => c i (y i)) = t then ∏ i, w i (y i) else 0 := by
  classical
  unfold categoricalAtom
  simp_rw [Fintype.prod_sum, Finset.ite_sum_zero, Fintype.prod_ite_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  let z : ι → J := fun i => c i (y i)
  have he (b : ι → J) : (∀ i, c i (y i) = b i) ↔ z = b := funext_iff.symm
  simp_rw [he]
  rw [Finset.sum_eq_single z]
  · simp [z]
    congr!
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

variable {n m k Δ : ℕ} {p : ℝ}

/-- The public coordinate law on the finite sorting alphabet. -/
private theorem coordNoise_fin (p : ℝ) (a b : Fin m) :
    coordNoise p a b = (if a = b then 1 - p else 0) + p / m := by
  by_cases h : a = b <;> simp [coordNoise, h, div_eq_mul_inv, add_comm]

private theorem return_le_atom {τ : Fin n → Option (Fin m × Fin n)}
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (x : Fin n → Fin m) {d : ℕ} (c : Fin n → Fin m → Fin d)
    (hcount : ∀ y, CorrectOn τ y → ∀ j, (univ.filter fun i => c i (x i) = j).card =
      (univ.filter fun i => c i (y i) = j).card) :
    (∑ y ∈ univ.filter (CorrectOn τ), noiseKernel p univ x y) ≤
      categoricalAtom (fun i j => ∑ v, if c i v = j then coordNoise p (x i) v else 0)
        (categoricalCount fun i => c i (x i)) := by
  classical
  rw [category_mass, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro y _
  by_cases hy : CorrectOn τ y
  · have he : categoricalCount (fun i => c i (y i)) = categoricalCount (fun i => c i (x i)) := by
      funext j
      simpa [categoricalCount] using (hcount y hy j).symm
    simp [hy, he, noiseKernel]
  · simp only [hy, ite_false]
    split
    · apply Finset.prod_nonneg
      intro i _
      rw [coordNoise_fin]
      exact add_nonneg (by split <;> linarith) (div_nonneg hp₀ (Nat.cast_nonneg _))
    · rfl

private theorem category_sum {J : Type} [Fintype J] [DecidableEq J] (hm : 0 < m)
    (p : ℝ) (x : Fin n → Fin m) (c : Fin n → Fin m → J) (i : Fin n) :
    (∑ j, ∑ v, if c i v = j then coordNoise p (x i) v else 0) = 1 := by
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, coordNoise_fin, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

private theorem category_lower {J : Type} [DecidableEq J] (hn : 0 < n) (hm : 0 < m)
    (hp₁ : p ≤ 1) (hp : 16 * (Δ : ℝ) / n ≤ p) (x : Fin n → Fin m) (c : Fin n → Fin m → J)
    (i : Fin n) (j : J) (hc : 15 * m ≤ 16 * Δ * (univ.filter fun v => c i v = j).card) :
    15 / (n : ℝ) ≤ ∑ v, if c i v = j then coordNoise p (x i) v else 0 := by
  let S := univ.filter fun v => c i v = j
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hc' : 15 * (m : ℝ) ≤ 16 * Δ * S.card := by exact_mod_cast hc
  rw [← Finset.sum_filter]
  calc
    15 / (n : ℝ) ≤ (S.card : ℝ) * ((16 * (Δ : ℝ) / n) / m) := by
      field_simp
      linarith
    _ ≤ S.card * (p / (m : ℝ)) := by gcongr
    _ = ∑ _ ∈ S, p / (m : ℝ) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro v _
      rw [coordNoise_fin, le_add_iff_nonneg_left]
      split <;> linarith

/-- Lemma 5.11 for the mission noise kernel. The probability of returning to the
partial sorting event is at most 2^(2-k). -/
theorem widelySpaced_noiseKernel_le {τ : Fin n → Option (Fin m × Fin n)} {x : Fin n → Fin m}
    (hm : n ^ 2 ≤ m) (hk : 4 ≤ k) (hkΔ : k ≤ Δ) (hΔn : 32 * Δ ≤ n)
    (hp : 16 * (Δ : ℝ) / n ≤ p) (hp₁ : p ≤ 1)
    {I : Finset (Fin n)} (hI : I ⊆ claimDomain τ) (hcard : I.card = k)
    (hsep : SpacedOn τ I Δ) (hx : CorrectOn τ x) :
    (∑ y ∈ univ.filter (CorrectOn τ), noiseKernel p univ x y) ≤ (2 : ℝ) ^ (2 - (k : ℝ)) := by
  classical
  have hn : 0 < n := by omega
  have hnm : n ≤ m := (Nat.le_self_pow (by decide : 2 ≠ 0) n).trans hm
  obtain ⟨c, hc, hcount⟩ := exists_gapCategories_of_widelySpaced
    (d := k - 2) hx hI (by omega) hsep (by omega)
  have hp₀ : 0 ≤ p := le_trans (by positivity) hp
  let P (i : Fin n) (j : Fin (k - 2 + 1)) := ∑ v, if c i v = j then coordNoise p (x i) v else 0
  have h := poissonMultinomial_atom_le_of_bernoulli hn (Nat.succ_pos _) bernoulliAtomBound_one
    zero_le_one (by positivity : 0 < 15 / (n : ℝ)) P (category_sum (by omega) p x c)
    (fun i j => category_lower hn (by omega) hp₁ hp x c i j (hc i j))
    (categoricalCount fun i => c i (x i))
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [one_mul, div_mul_cancel₀ _ hn', Nat.add_one_sub_one] at h
  have hbase : Real.sqrt (Real.exp 1) / Real.sqrt 15 ≤ 1 / 2 := by
    apply (div_le_iff₀ (Real.sqrt_pos.2 (by norm_num))).2
    calc
      Real.sqrt (Real.exp 1) ≤ Real.sqrt (15 / 4) := Real.sqrt_le_sqrt (by linarith [Real.exp_one_lt_three])
      _ = 1 / 2 * Real.sqrt 15 := by rw [Real.sqrt_div (by norm_num)]; norm_num; ring
  have he : 2 - (k : ℝ) = -((k - 2 : ℕ) : ℝ) := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [he, Real.rpow_neg (by norm_num), Real.rpow_natCast]
  simpa only [one_div, inv_pow] using
    ((return_le_atom hp₀ hp₁ x c hcount).trans h).trans (pow_le_pow_left₀ (by positivity) hbase _)

/-- The same return bound with the independent coordinate probabilities explicit. -/
theorem widelySpaced_return_le {τ : Fin n → Option (Fin m × Fin n)} {x : Fin n → Fin m}
    (hm : n ^ 2 ≤ m) (hk : 4 ≤ k) (hkΔ : k ≤ Δ) (hΔn : 32 * Δ ≤ n)
    (hp : 16 * (Δ : ℝ) / n ≤ p) (hp₁ : p ≤ 1)
    {I : Finset (Fin n)} (hI : I ⊆ claimDomain τ) (hcard : I.card = k)
    (hsep : SpacedOn τ I Δ) (hx : CorrectOn τ x) :
    (∑ y ∈ univ.filter (CorrectOn τ),
      ∏ i, ((if x i = y i then 1 - p else 0) + p / m)) ≤ (2 : ℝ) ^ (2 - (k : ℝ)) := by
  simpa only [noiseKernel, mem_univ, ite_true, coordNoise_fin] using
    widelySpaced_noiseKernel_le hm hk hkΔ hΔn hp hp₁ hI hcard hsep hx

end QNoiseStab.Supplement
end

-- Paper.TimeSpace.Claims
section
/-! Correctness of outputs written at arbitrary times and indices. -/

namespace QuantumNoiseStability.TimeSpace

open Finset

variable {C Y : Type*} [DecidableEq C]

/-- The coordinates of a list of claims. -/
def coords (l : List (C × Y)) : Finset C := (l.map Prod.fst).toFinset

theorem mem_coords {l : List (C × Y)} {c : C} : c ∈ coords l ↔ ∃ b, (c, b) ∈ l := by
  unfold coords
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨c', b⟩, h, rfl⟩
    exact ⟨b, h⟩
  · rintro ⟨b, h⟩
    exact ⟨(c, b), h, rfl⟩

theorem coords_append (l l' : List (C × Y)) : coords (l ++ l') = coords l ∪ coords l' := by
  unfold coords
  rw [List.map_append, List.toFinset_append]

/-- A short run succeeds when it commits to at least `k` distinct coordinates
and all of its claims agree with the target. -/
def ShortSuccess (k : ℕ) (target : C → Y) (l : List (C × Y)) : Prop :=
  k ≤ (coords l).card ∧ ∀ p ∈ l, target p.1 = p.2

/-- Every coordinate must be produced, and every value ever committed must be correct. -/
def FullSuccess (target : C → Y) (l : List (C × Y)) : Prop :=
  (∀ c, ∃ y, (c, y) ∈ l) ∧ ∀ p ∈ l, target p.1 = p.2

/-- **Pigeonhole over slices.** If the records of `ls` together claim every coordinate of
`C` correctly and `|C| > |ls| (k - 1)`, then some record in `ls` has at least `k` distinct
correct claims, hence satisfies the short event. -/
theorem exists_shortSuccess_of_cover (k : ℕ) (a : C → Y) :
    ∀ (ls : List (List (C × Y))) (s : Finset C),
      (∀ c ∈ s, ∃ b, (c, b) ∈ ls.flatten) → (∀ p ∈ ls.flatten, a p.1 = p.2) →
      ls.length * (k - 1) < s.card → ∃ l ∈ ls, ShortSuccess k a l
  | [], s, hcover, _, hcard => by
    exfalso
    have : s = ∅ := by
      ext c
      simp only [Finset.notMem_empty, iff_false]
      intro hc
      obtain ⟨b, hb⟩ := hcover c hc
      simp at hb
    rw [this] at hcard
    simp at hcard
  | l :: ls, s, hcover, hcorrect, hcard => by
    simp only [List.flatten_cons, List.mem_append] at hcover hcorrect
    by_cases hk : k ≤ (coords l).card
    · exact ⟨l, List.mem_cons_self, ⟨hk, fun p hp => hcorrect p (Or.inl hp)⟩⟩
    · push Not at hk
      have hrest := exists_shortSuccess_of_cover k a ls (s \ coords l) ?_ ?_ ?_
      · obtain ⟨l', hl', hs⟩ := hrest
        exact ⟨l', List.mem_cons_of_mem _ hl', hs⟩
      · intro c hc
        rw [Finset.mem_sdiff] at hc
        obtain ⟨b, hb⟩ := hcover c hc.1
        rcases hb with hb | hb
        · exact absurd (mem_coords.mpr ⟨b, hb⟩) hc.2
        · exact ⟨b, hb⟩
      · intro p hp
        exact hcorrect p (Or.inr hp)
      · have h1 := Finset.card_sdiff_add_card_inter s (coords l)
        have h2 : (s ∩ coords l).card ≤ (coords l).card :=
          Finset.card_le_card Finset.inter_subset_right
        simp only [List.length_cons] at hcard
        have : (ls.length + 1) * (k - 1) = ls.length * (k - 1) + (k - 1) := by ring
        omega

end QuantumNoiseStability.TimeSpace
end

-- Solutions.SortingBins
section
/-! # Equal-width sorting bins on a finite alphabet -/

namespace QNoiseStab.Supplement

/-- The bin of a letter in an alphabet of size `m`, numbered from zero. -/
def sortingBin {m Δ : ℕ} (hΔ : 0 < Δ) (v : Fin m) : Fin Δ :=
  ⟨Δ * v.val / m, (Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt v.isLt)).2
    (Nat.mul_lt_mul_of_pos_left v.isLt hΔ)⟩

@[simp] theorem sortingBin_val {m Δ : ℕ} (hΔ : 0 < Δ) (v : Fin m) :
    (sortingBin hΔ v).val = Δ * v.val / m := rfl

private theorem sortingBin_bounds {m Δ : ℕ} (hΔ : 0 < Δ) (v : Fin m) :
    (sortingBin hΔ v).val * m ≤ Δ * v.val ∧
      Δ * v.val < (sortingBin hΔ v).val * m + m :=
  ⟨Nat.div_mul_le_self _ _, Nat.lt_div_mul_add (Nat.zero_lt_of_lt v.isLt)⟩

/-- Each bin contains at most `m / Δ + 1` letters, with natural-number division. -/
theorem sortingBin_card_le {m Δ : ℕ} (hΔ : 0 < Δ) (b : Fin Δ) :
    (Finset.univ.filter (fun v : Fin m => sortingBin hΔ v = b)).card ≤ m / Δ + 1 := by
  let s := Finset.univ.filter (fun v : Fin m => sortingBin hΔ v = b)
  change s.card ≤ _
  by_cases hs : s.Nonempty
  · let u := s.min' hs
    have hu : sortingBin hΔ u = b := (Finset.mem_filter.mp (s.min'_mem hs)).2
    have lower := (sortingBin_bounds hΔ u).1
    rw [hu] at lower
    -- Subtract the least letter to inject the bin into the indicated range.
    rw [← Finset.card_range (m / Δ + 1)]
    apply Finset.card_le_card_of_injOn (fun v : Fin m => v.val - u.val)
    · intro v hv
      have upper := (sortingBin_bounds hΔ v).2
      rw [(Finset.mem_filter.mp hv).2] at upper
      apply Finset.mem_range.mpr
      apply Nat.lt_succ_of_le
      apply (Nat.le_div_iff_mul_le hΔ).2
      rw [Nat.mul_comm, Nat.mul_sub]
      omega
    · intro v hv w hw heq
      have hv' : u.val ≤ v.val := s.min'_le v hv
      have hw' : u.val ≤ w.val := s.min'_le w hw
      apply Fin.ext
      dsimp at heq
      omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

/-- The fraction of letters in any `2 * k` or fewer bins is at most `4 * k / Δ`. -/
theorem sortingBin_density_le {m Δ k : ℕ} (hΔ : 0 < Δ) (hΔm : Δ ≤ m)
    (B : Finset (Fin Δ)) (hB : B.card ≤ 2 * k) :
    ((Finset.univ.filter (fun v : Fin m => sortingBin hΔ v ∈ B)).card : ℝ) / m ≤
      4 * (k : ℝ) / Δ := by
  have hcard : (Finset.univ.filter (fun v : Fin m => sortingBin hΔ v ∈ B)).card ≤
      2 * k * (m / Δ + 1) := by
    rw [← Finset.sum_card_fiberwise_eq_card_filter]
    calc
      _ ≤ ∑ _b ∈ B, (m / Δ + 1) := Finset.sum_le_sum fun b _ => sortingBin_card_le hΔ b
      _ = B.card * (m / Δ + 1) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hB
  have hwidth : (m / Δ + 1) * Δ ≤ 2 * m := by
    rw [Nat.add_mul, Nat.one_mul]
    have := Nat.div_mul_le_self m Δ
    omega
  apply (div_le_div_iff₀ (by exact_mod_cast hΔ.trans_le hΔm) (by exact_mod_cast hΔ)).2
  exact_mod_cast calc
    _ ≤ (2 * k * (m / Δ + 1)) * Δ := Nat.mul_le_mul_right Δ hcard
    _ = 2 * k * ((m / Δ + 1) * Δ) := Nat.mul_assoc ..
    _ ≤ 2 * k * (2 * m) := Nat.mul_le_mul_left _ hwidth
    _ = 4 * k * m := by ring

/-- Letters with at least one bin strictly between their bins are widely separated. -/
theorem sortingBin_separated_of_gap {m Δ : ℕ} (hΔ : 0 < Δ) {v w : Fin m}
    (hgap : (sortingBin hΔ v).val + 2 ≤ (sortingBin hΔ w).val) :
    m < Δ * Nat.dist v.val w.val := by
  have upper := (sortingBin_bounds hΔ v).2
  have lower := (sortingBin_bounds hΔ w).1
  have h := Nat.mul_le_mul_right m hgap
  rw [Nat.add_mul] at h
  have hdist := Nat.mul_le_mul_left Δ (Nat.dist_tri_right v.val w.val)
  rw [Nat.mul_add] at hdist
  omega

/-- If no `k` transcript positions have pairwise widely separated values, the occupied
bins cover the transcript using at most `2 * (k - 1)` bins. -/
theorem exists_sortingBin_cover {m Δ n k : ℕ} (hΔ : 0 < Δ)
    (D : Finset (Fin n)) (a : Fin n → Fin m)
    (hno : ¬ ∃ S : Finset (Fin n), S ⊆ D ∧ S.card = k ∧
      (S : Set (Fin n)).Pairwise (fun i j => m < Δ * Nat.dist (a i).val (a j).val)) :
    ∃ B : Finset (Fin Δ), B.card ≤ 2 * (k - 1) ∧ ∀ i ∈ D, sortingBin hΔ (a i) ∈ B := by
  classical
  let f := fun i => sortingBin hΔ (a i)
  let B := D.image f
  refine ⟨B, ?_, fun i hi => Finset.mem_image_of_mem f hi⟩
  -- From k occupied bins of one parity, take one transcript position per bin.
  have parityBound (T : Finset (Fin Δ)) (hT : T ⊆ B)
      (hp : ∀ b ∈ T, ∀ c ∈ T, b.val % 2 = c.val % 2) : T.card ≤ k - 1 := by
    by_contra! h
    obtain ⟨U, hUT, hUk⟩ := Finset.exists_subset_card_eq (show k ≤ T.card by omega)
    have hsurj : (D : Set (Fin n)).SurjOn f U := by
      intro b hb
      exact Finset.mem_image.mp (hT (hUT hb))
    obtain ⟨S, hSD, hinj, himg⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn _ _ hsurj
    refine hno ⟨S, hSD, ?_, ?_⟩
    · rw [← Finset.card_image_of_injOn hinj, himg, hUk]
    · intro i hi j hj hij
      have hmem (x) (hx : x ∈ S) : f x ∈ T := by
        apply hUT
        rw [← himg]
        exact Finset.mem_image_of_mem _ hx
      have hmod := hp _ (hmem i hi) _ (hmem j hj)
      have hne : (f i).val ≠ (f j).val := fun heq => hij (hinj hi hj (Fin.ext heq))
      rcases (show (f i).val + 2 ≤ (f j).val ∨ (f j).val + 2 ≤ (f i).val by omega) with h | h
      · exact sortingBin_separated_of_gap hΔ h
      · rw [Nat.dist_comm]
        exact sortingBin_separated_of_gap hΔ h
  let even := fun b : Fin Δ => b.val % 2 = 0
  have he := parityBound (B.filter even) (Finset.filter_subset ..) (by
    intro b hb c hc
    exact (Finset.mem_filter.mp hb).2.trans (Finset.mem_filter.mp hc).2.symm)
  have ho := parityBound (B.filter fun b => ¬ even b) (Finset.filter_subset ..) (by
    intro b hb c hc
    have hb' : b.val % 2 ≠ 0 := (Finset.mem_filter.mp hb).2
    have hc' : c.val % 2 ≠ 0 := (Finset.mem_filter.mp hc).2
    omega)
  have := B.card_filter_add_card_filter_not even
  omega

/-- Number of candidate bin covers with at most `2 * k` bins. -/
theorem sortingBin_cover_count_le {Δ : ℕ} (hΔ : 2 ≤ Δ) (k : ℕ) :
    (Finset.univ.filter (fun B : Finset (Fin Δ) => B.card ≤ 2 * k)).card ≤ Δ ^ (2 * k + 1) := by
  have hsum (r : ℕ) : (∑ j ∈ Finset.range (r + 1), Δ ^ j) ≤ Δ ^ (r + 1) := by
    induction r with
    | zero => simpa using (show 1 ≤ Δ by omega)
    | succ r ih =>
      rw [Finset.sum_range_succ, pow_succ Δ (r + 1)]
      calc
        _ ≤ Δ ^ (r + 1) + Δ ^ (r + 1) := Nat.add_le_add_right ih _
        _ = Δ ^ (r + 1) * 2 := by omega
        _ ≤ _ := Nat.mul_le_mul_left _ hΔ
  let sets := fun j => (Finset.univ : Finset (Fin Δ)).powersetCard j
  calc
    _ ≤ ((Finset.range (2 * k + 1)).biUnion sets).card := by
      apply Finset.card_le_card
      intro B hB
      exact Finset.mem_biUnion.mpr ⟨B.card, Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Finset.mem_filter.mp hB).2), Finset.mem_powersetCard.mpr
          ⟨Finset.subset_univ _, rfl⟩⟩
    _ ≤ ∑ j ∈ Finset.range (2 * k + 1), (sets j).card := Finset.card_biUnion_le
    _ ≤ ∑ j ∈ Finset.range (2 * k + 1), Δ ^ j := by
      apply Finset.sum_le_sum
      intro j _
      simpa [sets, Finset.card_powersetCard] using Nat.choose_le_pow Δ j
    _ ≤ _ := hsum _

end QNoiseStab.Supplement
end

-- Solutions.SortingOutputs
section
/-! A successful sorting transcript either contains widely spaced claims or names
many values in a small union of alphabet bins. -/

namespace QNoiseStab.Supplement

open QuantumNoiseStability.TimeSpace
open scoped Classical

variable {n m : ℕ}

abbrev SortingClaims (n m : ℕ) := List (Fin n × (Fin m × Fin n))

/-- Read one value and rank per input index. Repeated commits are still all
checked by the success predicate. -/
def sortingOutput (l : SortingClaims n m) (i : Fin n) : Option (Fin m × Fin n) := l.lookup i

theorem claimDomain_sortingOutput (l : SortingClaims n m) :
    claimDomain (sortingOutput l) = coords l := by
  ext i
  simp only [claimDomain, Finset.mem_filter, Finset.mem_univ, true_and, sortingOutput,
    mem_coords, Option.isSome_iff_exists]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨u, v, e, _⟩ := List.lookup_eq_some_iff.mp ha
    exact ⟨a, by simp [e]⟩
  · rintro ⟨a, ha⟩
    by_contra! h
    have he : l.lookup i = none := Option.eq_none_iff_forall_ne_some.mpr h
    have hkeys := List.lookup_eq_none_iff.mp he (i, a) ha
    simp at hkeys

theorem correctOn_sortingOutput {x : Fin n → Fin m} {l : SortingClaims n m}
    (h : ∀ p ∈ l, sortFun x p.1 = p.2) : CorrectOn (sortingOutput l) x := by
  intro i a ha
  obtain ⟨u, v, e, _⟩ := List.lookup_eq_some_iff.mp ha
  exact h (i, a) (by simp [e])

def sortingClaimValue [NeZero m] (l : SortingClaims n m) (i : Fin n) : Fin m :=
  ((sortingOutput l i).map Prod.fst).getD 0

theorem sortingClaimValue_eq [NeZero m] {l : SortingClaims n m} {x : Fin n → Fin m}
    (h : CorrectOn (sortingOutput l) x) {i : Fin n} (hi : i ∈ coords l) :
    sortingClaimValue l i = x i := by
  rw [← claimDomain_sortingOutput] at hi
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp hi).2
  simpa [sortingClaimValue, ha, sortFun] using (congrArg Prod.fst (h i a ha)).symm

def WidelyClaimed [NeZero m] (Δ k : ℕ) (l : SortingClaims n m) : Prop :=
  ∃ I : Finset (Fin n), I ⊆ coords l ∧ I.card = k ∧
    (I : Set (Fin n)).Pairwise (fun i j =>
      m < Δ * Nat.dist (sortingClaimValue l i).val (sortingClaimValue l j).val)

theorem widelyClaimed_spacedOn [NeZero m] {Δ k : ℕ} {l : SortingClaims n m}
    (h : WidelyClaimed Δ k l) : ∃ I ⊆ claimDomain (sortingOutput l), I.card = k ∧
      SpacedOn (sortingOutput l) I Δ := by
  obtain ⟨I, hI, hc, hs⟩ := h
  refine ⟨I, by simpa [claimDomain_sortingOutput] using hI, hc, ?_⟩
  intro i hi j hj hij a b ha hb
  simpa [sortingClaimValue, ha, hb] using hs hi hj hij

noncomputable def selectedClaims {K Y : Type} [Fintype K] [DecidableEq K]
    (s : ℕ) (l : List (K × Y)) : Finset K :=
  if h : s ≤ (coords l).card then (Finset.exists_subset_card_eq h).choose else ∅

theorem selectedClaims_spec {K Y : Type} [Fintype K] [DecidableEq K] {s : ℕ}
    {l : List (K × Y)} (h : s ≤ (coords l).card) :
    selectedClaims s l ⊆ coords l ∧ (selectedClaims s l).card = s := by
  simpa [selectedClaims, h] using (Finset.exists_subset_card_eq h).choose_spec

/-- The alternative used for a union bound over the possible subsets of bins.
The selected coordinates are a function of the transcript. -/
theorem sorting_claims_dichotomy [NeZero m] {k Δ s : ℕ} (hΔ : 0 < Δ)
    (x : Fin n → Fin m) (l : SortingClaims n m) (hs : ShortSuccess s (sortFun x) l) :
    (CorrectOn (sortingOutput l) x ∧ WidelyClaimed Δ k l) ∨
      ∃ B : Finset (Fin Δ), B.card ≤ 2 * k ∧ s ≤ (coords l).card ∧
        ∀ i ∈ selectedClaims s l, sortingBin hΔ (x i) ∈ B := by
  classical
  have hc := correctOn_sortingOutput hs.2
  by_cases hw : WidelyClaimed Δ k l
  · exact Or.inl ⟨hc, hw⟩
  · obtain ⟨B, hB, hcov⟩ := exists_sortingBin_cover hΔ (coords l) (sortingClaimValue l) hw
    refine Or.inr ⟨B, by omega, hs.1, ?_⟩
    intro i hi
    have hid := (selectedClaims_spec hs.1).1 hi
    simpa only [sortingClaimValue_eq hc hid] using hcov i hid

/-- A finite union bound on events of the measured execution. -/
theorem success_cover_le {W G O J : Type} [Fintype W] [Fintype G] (I : Finset J)
    (c : List (Step W (Fin n) G O)) (v : State W) (H A : (Fin n → G) → List O → Prop)
    (B : J → (Fin n → G) → List O → Prop)
    (hcover : ∀ x l, H x l → A x l ∨ ∃ j ∈ I, B j x l) :
    success c v H ≤ success c v A + ∑ j ∈ I, success c v (B j) := by
  classical
  let mass (P : (Fin n → G) → List O → Prop) (x : Fin n → G) (h : Hist c) :=
    if P x (claims c h) then ‖run c x v h‖ ^ 2 else 0
  have hpos (P x h) : 0 ≤ mass P x h := by dsimp [mass]; split <;> positivity
  have commute : (∑ j ∈ I, ∑ x, ∑ h, mass (B j) x h) = ∑ x, ∑ h, ∑ j ∈ I, mass (B j) x h := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
  unfold success eventMass
  change _ ≤ _ * (∑ x, ∑ h, mass A x h) + ∑ j ∈ I, _ * (∑ x, ∑ h, mass (B j) x h)
  rw [← Finset.mul_sum, ← mul_add, commute, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro x _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro h _
  by_cases hH : H x (claims c h)
  · rcases hcover _ _ hH with hA | ⟨j,hj,hB⟩
    · simp only [hH, ite_true]
      exact (show ‖run c x v h‖ ^ 2 = mass A x h by simp [mass, hA]).le.trans
        (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => hpos _ _ _))
    · simp only [hH, ite_true]
      exact (show ‖run c x v h‖ ^ 2 = mass (B j) x h by simp [mass, hB]).le.trans
        ((Finset.single_le_sum (f := fun j => mass (B j) x h) (fun _ _ => hpos _ _ _) hj).trans
          (le_add_of_nonneg_left (hpos _ _ _)))
  · simp only [hH, ite_false]
    exact add_nonneg (hpos _ _ _) (Finset.sum_nonneg fun _ _ => hpos _ _ _)

end QNoiseStab.Supplement
end

-- Solutions.SortingScales
section
/-! Numerical parameters for the wide and rare-bin cases of a sorting slice. -/


set_option autoImplicit false

namespace QNoiseStab.Supplement

open Filter Real

/-- A single bin contributes at most `b ^ (2 * s)`. The width pays for the
`Δ ^ (2 * k + 1)` possible choices of bins and leaves a factor of `2 ^ (-k)`. -/
theorem sorting_bin_union {n Δ b : ℝ} {k s : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hΔ : 0 ≤ Δ) (hΔn : Δ ≤ n) (hb : 0 ≤ b) (hbase : b ≤ exp (-(log (log n) / 2)))
    (hwidth : 4 * k * log n ≤ s * log (log n)) :
    Δ ^ (2 * k + 1) * b ^ (2 * s) ≤ (2 : ℝ) ^ (-(k : ℝ)) := by
  have hn0 : 0 < n := by linarith
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hcount := mul_le_mul_of_nonneg_right hk' (log_nonneg (by linarith : 1 ≤ n))
  have hlog := mul_le_mul_of_nonneg_left (log_le_log (by norm_num : (0 : ℝ) < 2) hn)
    (Nat.cast_nonneg k)
  calc
    _ ≤ n ^ (2 * k + 1) * exp (-(log (log n) / 2)) ^ (2 * s) :=
      mul_le_mul (pow_le_pow_left₀ hΔ hΔn _) (pow_le_pow_left₀ hb hbase _) (by positivity)
        (by positivity)
    _ = exp (((2 * k + 1 : ℕ) : ℝ) * log n + ((2 * s : ℕ) : ℝ) * (-(log (log n) / 2))) := by
      rw [exp_add, exp_nat_mul, exp_log hn0, exp_nat_mul]
    _ ≤ _ := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), exp_le_exp]
      push_cast
      linarith only [hwidth, hcount, hlog]

/-- Rounded logarithmic factor in the output width. -/
noncomputable def sortingLogFactor (n : ℕ) : ℕ := ⌈log n / log (log n)⌉₊

/-- Eventually the rounded logarithmic factor is at least `M * sqrt (log n)`. -/
private theorem eventually_sortingLogFactor {M : ℝ} (hM : 1 ≤ M) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 0 < log (log (n : ℝ)) ∧ 4 ≤ (sortingLogFactor n : ℝ) ∧
      M * exp (log (log (n : ℝ)) / 2) ≤ sortingLogFactor n ∧
      (sortingLogFactor n : ℝ) ≤ 2 * (log n / log (log n)) := by
  have hg : Tendsto (fun n : ℕ => log (log (n : ℝ))) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop 2, hg.eventually_ge_atTop (8 * M)] with n hn hlarge
  let u := log (log (n : ℝ))
  change 8 * M ≤ u at hlarge
  have hu : 0 < u := by linarith
  have hnlog : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < n))
  have hquad := quadratic_le_exp_of_nonneg (show 0 ≤ u / 2 by linarith)
  have hMu : M * u ≤ exp (u / 2) := by
    nlinarith only [hquad, mul_le_mul_of_nonneg_right hlarge hu.le, hu.le]
  have hlog : exp (u / 2) * exp (u / 2) = log n := by
    rw [← exp_add, add_halves, exp_log hnlog]
  have hratio : M * exp (u / 2) ≤ log n / u := by
    apply (le_div_iff₀ hu).mpr
    linarith only [mul_le_mul_of_nonneg_right hMu (exp_pos (u / 2)).le, hlog]
  have hfour : 4 ≤ M * exp (u / 2) := by
    have h := mul_le_mul_of_nonneg_right hM (exp_pos (u / 2)).le
    linarith [add_one_le_exp (u / 2)]
  have hlo : log n / u ≤ (sortingLogFactor n : ℝ) := Nat.le_ceil _
  refine ⟨hn, hu, hfour.trans (hratio.trans hlo), hratio.trans hlo, ?_⟩
  have hceil := Nat.ceil_lt_add_one (div_nonneg hnlog.le hu.le)
  change (⌈log (n : ℝ) / u⌉₊ : ℝ) ≤ 2 * (log n / u)
  linarith

private theorem sorting_cube_scales {n k : ℝ} (hn : 0 < n) (hk : 0 < k) :
    let x := (n / k) ^ (1 / 3 : ℝ)
    n = k * x ^ 3 ∧ k ^ (2 / 3 : ℝ) * n ^ (1 / 3 : ℝ) = k * x ∧
      k ^ (1 / 3 : ℝ) * n ^ (2 / 3 : ℝ) = k * x ^ 2 := by
  dsimp only
  have scale (a : ℝ) : k ^ (1 - a) * n ^ a = k * (n / k) ^ a := by
    rw [rpow_sub hk, rpow_one, div_rpow hn.le hk.le]
    ring
  have power (d : ℕ) : ((n / k) ^ (1 / 3 : ℝ)) ^ d = (n / k) ^ ((d : ℝ) / 3) := by
    rw [← rpow_mul_natCast (div_nonneg hn.le hk.le)]
    congr 1
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [power]
    norm_num
    exact (mul_div_cancel₀ n hk.ne').symm
  · convert scale (1 / 3) using 2
    norm_num
  · rw [power]
    convert scale (2 / 3) using 2 <;> norm_num

/-- The output width has this upper bound uniformly in the space parameter. -/
theorem sorting_width_upper : ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
    ((4 * k * sortingLogFactor n : ℕ) : ℝ) ≤ 8 * k * (log n / log (log n)) := by
  filter_upwards [eventually_sortingLogFactor (M := 1) le_rfl] with n hn k
  obtain ⟨_, _, _, _, hceil⟩ := hn
  push_cast
  linarith only [mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg k)]

private theorem sorting_wide_factor {p : ℝ} {t k : ℕ} (hp : 0 ≤ p) (hp' : p ≤ 1 / 2)
    (hpt : 2 * p * t ≤ k / 16) : ((1 - p) ^ t)⁻¹ ≤ exp ((k : ℝ) / 16) := by
  have h : (1 - p)⁻¹ ≤ 1 + 2 * p := by
    rw [inv_le_iff_one_le_mul₀ (by linarith)]
    nlinarith only [mul_nonneg hp (show 0 ≤ 1 / 2 - p by linarith)]
  rw [← inv_pow]
  calc
    _ ≤ exp (2 * p) ^ t := pow_le_pow_left₀ (inv_nonneg.mpr (by linarith))
      (h.trans (by linarith [add_one_le_exp (2 * p)])) _
    _ ≤ _ := by rw [← exp_nat_mul, exp_le_exp]; linarith

/-- The two numerical error bounds together give success exponent `γ = 1 / 8`. -/
private theorem sorting_slice_error {k Δ a : ℝ} (hk : 4 ≤ k) (hΔ : k ≤ Δ)
    (ha : a ≤ exp (k / 16)) :
    a * (exp (-2 * Δ) + (2 : ℝ) ^ (2 - k)) + (2 : ℝ) ^ (-k) ≤
      (2 : ℝ) ^ (-(k / 8)) := by
  have hlog : 1 / 2 ≤ log 2 := by
    have h := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    linarith
  have hlog' : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have htail : exp (-2 * Δ) ≤ (2 : ℝ) ^ (-k) := by
    rw [rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), exp_le_exp]
    nlinarith only [hΔ, mul_le_mul_of_nonneg_right hlog' (show 0 ≤ k by linarith), hk]
  have hamp : exp (k / 16) ≤ (2 : ℝ) ^ (k / 8) := by
    rw [rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), exp_le_exp]
    linarith only [mul_le_mul_of_nonneg_right hlog (show 0 ≤ k by linarith)]
  have hone : 1 ≤ (2 : ℝ) ^ (k / 8) := one_le_rpow (by norm_num) (by linarith)
  have hfour : (2 : ℝ) ^ (2 - k) = 4 * (2 : ℝ) ^ (-k) := by
    rw [sub_eq_add_neg, rpow_add (by norm_num)]
    norm_num
  have hcost : 6 ≤ (2 : ℝ) ^ (3 * k / 4) := calc
    _ ≤ (2 : ℝ) ^ (3 : ℝ) := by norm_num
    _ ≤ _ := rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  calc
    _ ≤ (2 : ℝ) ^ (k / 8) * (5 * (2 : ℝ) ^ (-k)) + (2 : ℝ) ^ (-k) := by
      rw [hfour]
      gcongr
      · exact ha.trans hamp
      · linarith only [htail]
    _ ≤ 6 * ((2 : ℝ) ^ (k / 8) * (2 : ℝ) ^ (-k)) := by
      linarith only [mul_le_mul_of_nonneg_right hone (rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-k))]
    _ ≤ (2 : ℝ) ^ (3 * k / 4) * ((2 : ℝ) ^ (k / 8) * (2 : ℝ) ^ (-k)) :=
      mul_le_mul_of_nonneg_right hcost (by positivity)
    _ = _ := by
      rw [← rpow_add (by norm_num : (0 : ℝ) < 2), ← rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

/-- Bounds for the integer parameters used by the two cases of a sorting slice. -/
structure SortingSliceScales (M : ℝ) (n k Δ t s : ℕ) : Prop where
  le_spacing : k ≤ Δ
  spacing_le : 32 * Δ ≤ n
  queries_pos : 0 < t
  queries_lower : (k : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) / 1024 ≤ t
  width_upper : (s : ℝ) ≤ 8 * k * (log n / log (log n))
  noise_pos : 0 < 16 * (Δ : ℝ) / n
  noise_le_half : 16 * (Δ : ℝ) / n ≤ 1 / 2
  wide : ((1 - 16 * (Δ : ℝ) / n) ^ t)⁻¹ ≤ exp ((k : ℝ) / 4)
  rare : (Δ : ℝ) ^ (2 * k + 1) * (M * (2 * t + s) * sqrt (4 * k / Δ) / s) ^ (2 * s) ≤
    (2 : ℝ) ^ (-(k : ℝ))
  combined : ((1 - 16 * (Δ : ℝ) / n) ^ t)⁻¹ *
      (exp (-2 * (Δ : ℝ)) + (2 : ℝ) ^ (2 - (k : ℝ))) + (2 : ℝ) ^ (-(k : ℝ)) ≤
    (2 : ℝ) ^ (-((k : ℝ) / 8))

/-- Take `α = 1 / 512` in both the admissible range and the query budget.
The width is four times the rounded logarithmic factor times `k`, and the
combined error is at most `2 ^ (-k / 8)`. Only the threshold depends on `M`. -/
theorem sorting_slice_parameters (M : ℝ) (hM : 1 ≤ M) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, 4 ≤ k →
      (k : ℝ) * (8 * (sortingLogFactor n : ℝ)) ^ 3 ≤ (1 / 512 : ℝ) * n →
      SortingSliceScales M n k
        ⌊(k : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ)⌋₊
        ⌊(1 / 512 : ℝ) * ((k : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ))⌋₊
        (4 * k * sortingLogFactor n) := by
  filter_upwards [eventually_sortingLogFactor hM, sorting_width_upper] with n hn hwidth
  obtain ⟨hn2, hll, hL4, hML, _⟩ := hn
  intro k hk hrange
  let L : ℝ := sortingLogFactor n
  let x := ((n : ℝ) / k) ^ (1 / 3 : ℝ)
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hk' : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hnx, htime, hspace⟩ := sorting_cube_scales hn0 hk0
  change (n : ℝ) = k * x ^ 3 at hnx
  change _ = k * x at htime
  change _ = k * x ^ 2 at hspace
  change 4 ≤ L at hL4
  have hxL : 64 * L ≤ x := by
    apply (Odd.strictMono_pow (by decide : Odd 3)).le_iff_le.mp
    apply le_of_mul_le_mul_left _ hk0
    change (k : ℝ) * (8 * L) ^ 3 ≤ 1 / 512 * n at hrange
    rw [hnx] at hrange
    linarith only [hrange]
  have hx : 256 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  let Δ := ⌊(k : ℝ) * x ^ 2⌋₊
  let t := ⌊(1 / 512 : ℝ) * (k * x)⌋₊
  let s := 4 * k * sortingLogFactor n
  rw [htime, hspace]
  change SortingSliceScales M n k Δ t s
  have hs : (s : ℝ) = 4 * k * L := by simp [s, L]
  have hs0 : (0 : ℝ) < s := by rw [hs]; positivity
  have hdub : (Δ : ℝ) ≤ k * x ^ 2 := Nat.floor_le (by positivity)
  have htub : (t : ℝ) ≤ (1 / 512 : ℝ) * (k * x) := Nat.floor_le (by positivity)
  have hdf : (k : ℝ) * x ^ 2 < Δ + 1 := Nat.lt_floor_add_one _
  have htf : (1 / 512 : ℝ) * (k * x) < t + 1 := Nat.lt_floor_add_one _
  have hkk : k ≤ Δ := by
    apply Nat.le_floor
    exact le_mul_of_one_le_right hk0.le (by nlinarith only [hx, sq_nonneg (x - 1)])
  have hd0 : (0 : ℝ) < Δ := by exact_mod_cast (show 0 < Δ by omega)
  have hd32 : 32 * (Δ : ℝ) ≤ n := by
    rw [hnx]
    nlinarith only [hdub, mul_nonneg (mul_nonneg hk0.le (sq_nonneg x))
      (show 0 ≤ x - 32 by linarith)]
  have htlo : (k : ℝ) * x / 1024 ≤ t := by
    linarith only [htf, mul_le_mul hk' hx (by norm_num : (0 : ℝ) ≤ 256) hk0.le]
  let p := 16 * (Δ : ℝ) / n
  have hp : 0 < p := by dsimp [p]; positivity
  have hp' : p ≤ 1 / 2 := (div_le_iff₀ hn0).mpr (by linarith)
  have hpt : 2 * p * t ≤ k / 16 := by
    dsimp [p]
    rw [← mul_div_assoc, div_mul_eq_mul_div, div_le_iff₀ hn0, hnx]
    nlinarith only [mul_le_mul hdub htub (Nat.cast_nonneg t) (by positivity)]
  have hwide := sorting_wide_factor hp.le hp' hpt
  refine ⟨hkk, by exact_mod_cast hd32, ?_, htime ▸ htlo, hwidth k, hp, hp',
    hwide.trans (exp_le_exp.mpr (by linarith)), ?_,
    sorting_slice_error hk' (by exact_mod_cast hkk) hwide⟩
  · exact_mod_cast (show (0 : ℝ) < t from lt_of_lt_of_le (by positivity) htlo)
  · -- The floors give sqrt (4k / Δ) ≤ 3 / x, and 2t + s ≤ kx.
    have hdhalf : (k : ℝ) * x ^ 2 ≤ 2 * Δ := by
      have : (1 : ℝ) ≤ Δ := by exact_mod_cast (show 1 ≤ Δ by omega)
      linarith
    have hsqrt : sqrt (4 * (k : ℝ) / Δ) ≤ 3 / x := by
      apply (Real.sqrt_le_left (by positivity)).mpr
      rw [div_pow, div_le_div_iff₀ hd0 (sq_pos_of_pos hx0)]
      nlinarith only [hdhalf, hd0]
    have hsum : 2 * (t : ℝ) + s ≤ k * x := by
      rw [hs]
      linarith only [htub, mul_le_mul_of_nonneg_left hxL hk0.le,
        mul_pos hk0 hx0]
    have hprod : (2 * (t : ℝ) + s) * sqrt (4 * k / Δ) ≤ 4 * k := calc
      _ ≤ (k * x) * (3 / x) := mul_le_mul hsum hsqrt (sqrt_nonneg _) (by positivity)
      _ = 3 * k := by field_simp
      _ ≤ _ := by linarith
    have hbase : M * (2 * (t : ℝ) + s) * sqrt (4 * k / Δ) / s ≤ M / L := by
      rw [div_le_div_iff₀ hs0 (by linarith : 0 < L)]
      calc
        _ = (M * ((2 * t + s) * sqrt (4 * k / Δ))) * L := by ring
        _ ≤ (M * (4 * k)) * L := by gcongr
        _ = _ := by rw [hs]; ring
    have hexp : M / L ≤ exp (-(log (log n) / 2)) := by
      rw [exp_neg, ← one_div, div_le_div_iff₀ (by linarith : 0 < L) (exp_pos _), one_mul]
      exact hML
    apply sorting_bin_union hn' (by omega) (Nat.cast_nonneg Δ) (by linarith only [hd32, hd0])
      (by positivity) (hbase.trans hexp)
    have hl : log n ≤ L * log (log n) := (div_le_iff₀ hll).mp (Nat.le_ceil _)
    rw [hs]
    linarith only [mul_le_mul_of_nonneg_left hl hk0.le]

end QNoiseStab.Supplement
end

-- Solutions.SortingMixture
section
/-!
# Uniform inputs from independent Bernoulli flags

Choose uniform vectors outside and inside a set `B`. In each coordinate, select
the inside value with probability `B.card / Fintype.card X`. The resulting vector
is uniform, and its membership in `B` recovers every flag.
-/


namespace QNoiseStab.Supplement

open Finset
open scoped BigOperators

variable {X : Type*} {n : ℕ}

/-- Select the inside or outside value at each coordinate according to the flag. -/
def mixtureInput (B : Finset X) (a : Fin n → {x // x ∉ B})
    (b : Fin n → {x // x ∈ B}) (t : Fin n → Bool) : Fin n → X :=
  fun i => if t i then (b i).val else (a i).val

@[simp] theorem mixtureInput_mem_iff (B : Finset X) (a : Fin n → {x // x ∉ B})
    (b : Fin n → {x // x ∈ B}) (t : Fin n → Bool) (i : Fin n) :
    mixtureInput B a b t i ∈ B ↔ t i = true := by
  cases h : t i <;> simp [mixtureInput, h, (a i).property, (b i).property]

/-- The probability of a flag vector under independent Bernoulli trials. -/
noncomputable def mixtureFlagWeight (p : ℝ) (t : Fin n → Bool) : ℝ :=
  ∏ i, if t i then p else 1 - p

private theorem prod_expect {Y : Type*} [Fintype Y] (f : Fin n → Y → ℝ) :
    (∏ i, 𝔼 z, f i z) = 𝔼 z : Fin n → Y, ∏ i, f i (z i) := by
  simp only [Fintype.expect_eq_sum_div_card, prod_div_distrib, Fintype.prod_sum,
    prod_const, card_univ, Fintype.card_fin, Fintype.card_fun, Nat.cast_pow]

variable [Fintype X] [DecidableEq X]

private theorem expect_coordinate [Nonempty X] (B : Finset X) (hB : B.Nonempty)
    (hproper : B ≠ univ) (f : X → ℝ) :
    let p : ℝ := B.card / Fintype.card X
    (𝔼 x, f x) = 𝔼 a : {x // x ∉ B}, 𝔼 b : {x // x ∈ B}, ∑ t : Bool,
      (if t then p else 1 - p) * f (if t then b.val else a.val) := by
  dsimp only
  have : Nonempty {x // x ∈ B} := hB.to_subtype
  have : Nonempty {x // x ∉ B} := by
    obtain ⟨x, hx⟩ := not_forall.mp (mt eq_univ_of_forall hproper)
    exact ⟨x, hx⟩
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true,
    expect_add_distrib, ← mul_expect, Fintype.expect_const]
  have hc : (Fintype.card {x // x ∉ B} : ℝ) = Fintype.card X - B.card := by
    rw [Fintype.card_subtype_compl, Nat.cast_sub (Fintype.card_subtype_le _),
      Fintype.card_coe]
  have hX : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hp : 1 - (B.card : ℝ) / Fintype.card X =
      (Fintype.card {x // x ∉ B} : ℝ) / Fintype.card X := by rw [hc]; field_simp
  rw [hp, ← Fintype.card_coe B]
  simp only [div_mul_eq_mul_div, Fintype.card_mul_expect, ← add_div]
  rw [Fintype.expect_eq_sum_div_card]
  congr 1
  convert! (Fintype.sum_subtype_add_sum_subtype (· ∈ B) f).symm

/-- The average of a real test over uniform inputs equals its average over two
independent uniform candidate vectors and independent Bernoulli flags. Each
`𝔼` is a finite sum divided by the cardinality of its domain. -/
theorem expect_mixtureInput [Nonempty X] (B : Finset X) (hB : B.Nonempty)
    (hproper : B ≠ univ) (F : (Fin n → X) → ℝ) :
    (𝔼 x, F x) = 𝔼 a, 𝔼 b, ∑ t : Fin n → Bool,
      mixtureFlagWeight (B.card / Fintype.card X) t * F (mixtureInput B a b t) := by
  let p : ℝ := B.card / Fintype.card X
  -- Factor a product test into its one-coordinate expectations.
  have product_test (f : Fin n → X → ℝ) :
      (𝔼 x : Fin n → X, ∏ i, f i (x i)) =
        𝔼 a, 𝔼 b, ∑ t : Fin n → Bool,
          mixtureFlagWeight p t * ∏ i, f i (mixtureInput B a b t i) := by
    rw [← prod_expect]
    simp_rw [expect_coordinate B hB hproper, prod_expect, Fintype.prod_sum,
      prod_mul_distrib]
    rfl
  -- Every test is a finite linear combination of point indicators.
  have point (y : Fin n → X) := product_test (fun i z => if z = y i then 1 else 0)

  calc
    (𝔼 x, F x) = ∑ y, (𝔼 x : Fin n → X, (if x = y then (1 : ℝ) else 0)) * F y := by
      simp_rw [expect_mul, ← expect_sum_comm]
      simp
    _ = ∑ y, (𝔼 a, 𝔼 b, ∑ t, mixtureFlagWeight p t *
        (if mixtureInput B a b t = y then (1 : ℝ) else 0)) * F y := by
      apply sum_congr rfl
      intro y _
      exact congrArg (· * F y) (by simpa only [Fintype.prod_boole, ← funext_iff] using point y)
    _ = _ := by
      simp_rw [expect_mul, sum_mul, ← expect_sum_comm]
      congr 1
      funext a
      congr 1
      funext b
      rw [sum_comm]
      simp [p]

/-- Joint form for tests of the input and its membership flags. For example, a
test can sum transcript probabilities over transcripts satisfying a predicate
of the transcript, the input, and the flags. -/
theorem expect_mixtureInput_flags [Nonempty X] (B : Finset X) (hB : B.Nonempty)
    (hproper : B ≠ univ) (F : (Fin n → X) → (Fin n → Bool) → ℝ) :
    (𝔼 x, F x (fun i => decide (x i ∈ B))) = 𝔼 a, 𝔼 b, ∑ t : Fin n → Bool,
      mixtureFlagWeight (B.card / Fintype.card X) t * F (mixtureInput B a b t) t := by
  simpa only [mixtureInput_mem_iff, Bool.decide_eq_true] using
    expect_mixtureInput B hB hproper (fun x => F x (fun i => decide (x i ∈ B)))

/-- For the empty set, sample just the outside vector and set every flag to false. -/
theorem expect_mixtureInput_empty (F : (Fin n → X) → (Fin n → Bool) → ℝ) :
    (𝔼 x, F x (fun i => decide (x i ∈ (∅ : Finset X)))) =
      𝔼 a : Fin n → {x // x ∉ (∅ : Finset X)}, F (fun i => (a i).val) (fun _ => false) := by
  let e := Equiv.subtypeUnivEquiv (fun x : X => notMem_empty x)
  symm
  apply Fintype.expect_equiv (Equiv.piCongrRight fun _ : Fin n => e)
  intro a
  simp only [notMem_empty, decide_false]
  rfl

end QNoiseStab.Supplement
end

-- Solutions.SortingBoolean
section
/-! Multilinear degree on the Boolean cube and the Bernoulli polynomial for
an event requiring a prescribed set of marked positions. -/

set_option autoImplicit false

namespace QNoiseStab.Supplement.SortingSearch

open Polynomial

variable {n : ℕ}

/-- A Boolean monomial with coefficient `c` and distinct variables indexed by `S`. -/
private noncomputable def term (S : Finset (Fin n)) (c : ℂ) (x : Fin n → Bool) : ℂ :=
  if ∀ i ∈ S, x i = true then c else 0

/-- Finite sums of multilinear monomials of degree at most `r` on the Boolean cube. -/
inductive Degree (r : ℕ) : ((Fin n → Bool) → ℂ) → Prop
  | mono (S : Finset (Fin n)) (c : ℂ) (h : S.card ≤ r) : Degree r (term S c)
  | add {f g} : Degree r f → Degree r g → Degree r (fun x => f x + g x)

theorem degree_const (r : ℕ) (c : ℂ) : Degree (n := n) r (fun _ => c) := by
  have h : term (∅ : Finset (Fin n)) c = fun _ => c := by funext x; simp [term]
  exact h ▸ Degree.mono ∅ c (by simp)

theorem degree_single (i : Fin n) (f : Bool → ℂ) :
    Degree 1 (fun x => f (x i)) := by
  have heq : (fun x : Fin n → Bool => f (x i)) =
      fun x => f false + term {i} (f true - f false) x := by
    funext x
    cases h : x i <;> simp [term, h]
  rw [heq]
  exact .add (degree_const _ _) (.mono _ _ (by simp))

private theorem term_mul (S U : Finset (Fin n)) (c d : ℂ) :
    (fun x => term S c x * term U d x) = term (S ∪ U) (c * d) := by
  funext x
  simp only [term, Finset.forall_mem_union]
  split_ifs <;> simp_all

theorem degree_mul {r t : ℕ} {f g : (Fin n → Bool) → ℂ}
    (hf : Degree r f) (hg : Degree t g) : Degree (r + t) (fun x => f x * g x) := by
  induction hf with
  | mono S c hS =>
    induction hg with
    | mono U d hU =>
      rw [term_mul]
      exact .mono _ _ ((Finset.card_union_le _ _).trans (Nat.add_le_add hS hU))
    | add _ _ ih₁ ih₂ => simpa only [mul_add] using Degree.add ih₁ ih₂
  | add _ _ ih₁ ih₂ => simpa only [add_mul] using Degree.add ih₁ ih₂

theorem degree_sum {ι : Type*} (S : Finset ι) {r : ℕ}
    (f : ι → (Fin n → Bool) → ℂ) (h : ∀ i, Degree r (f i)) :
    Degree r (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using degree_const (n := n) r 0
  | insert i S hi ih => simpa [hi] using Degree.add (h i) ih

/-- Under independent Bernoulli flags, the mass of assignments marking all of `S`
is `p ^ S.card`. The polynomial identity holds for every real `p`. -/
theorem marked_mass (S : Finset (Fin n)) (p : ℝ) :
    (∑ x : Fin n → Bool, (∏ i, if x i then p else 1 - p) *
      (if ∀ i ∈ S, x i = true then 1 else 0)) = p ^ S.card := by
  classical
  let factor (i : Fin n) (z : Bool) : ℝ :=
    if i ∈ S → z = true then (if z then p else 1 - p) else 0
  calc
    _ = ∑ x : Fin n → Bool, ∏ i, factor i (x i) := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [factor, Fintype.prod_ite_zero]
      split_ifs <;> simp_all
    _ = ∏ i, ∑ z : Bool, factor i z := (Fintype.prod_sum factor).symm
    _ = ∏ i : Fin n, if i ∈ S then p else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ S <;> simp [factor, hi]
    _ = _ := by simp

/-- Multiplying a monomial on `U` by the test on `J` gives the monomial on `U ∪ J`.
Its expectation has exponent between `J.card` and `r + J.card`. -/
theorem tested_polynomial {r : ℕ} {f : (Fin n → Bool) → ℂ}
    (hf : Degree r f) (J : Finset (Fin n)) :
    ∃ P : ℝ[X], P.natDegree ≤ r + J.card ∧ X ^ J.card ∣ P ∧
      ∀ p : ℝ, P.eval p = ∑ x : Fin n → Bool, (∏ i, if x i then p else 1 - p) *
        (if ∀ i ∈ J, x i = true then (f x).re else 0) := by
  classical
  induction hf with
  | mono U c hU =>
    refine ⟨C c.re * X ^ (U ∪ J).card,
      (natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le _).trans
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_right hU _))), ?_, ?_⟩
    · exact dvd_mul_of_dvd_right
        (pow_dvd_pow X (Finset.card_le_card Finset.subset_union_right)) _
    · intro p
      have h := congrArg (· * c.re) (marked_mass (U ∪ J) p)
      rw [Finset.sum_mul] at h
      simp only [eval_mul, eval_C, eval_pow, eval_X]
      rw [mul_comm, ← h]
      apply Finset.sum_congr rfl
      intro x _
      simp only [term, Finset.forall_mem_union]
      split_ifs <;> simp_all
  | add _ _ ih₁ ih₂ =>
    obtain ⟨P, hP, dP, eP⟩ := ih₁
    obtain ⟨Q, hQ, dQ, eQ⟩ := ih₂
    refine ⟨P + Q, natDegree_add_le_of_degree_le hP hQ, dvd_add dP dQ, ?_⟩
    intro p
    rw [eval_add, eP, eQ, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp [mul_add]

end QNoiseStab.Supplement.SortingSearch
end

-- Solutions.SortingStepSearch
section
/-! # Bernoulli marks in the generic step model -/

noncomputable section

namespace QuantumNoiseStability.TimeSpace

open QNoiseStab.Supplement.SortingSearch Polynomial
open scoped ComplexConjugate

variable {n : ℕ} {W G O : Type} [Fintype W]

private theorem degree_linearMap {r : ℕ} (L : State W →ₗ[ℂ] State W)
    (v : (Fin n → Bool) → State W) (hv : ∀ w, Degree r (fun x => v x w)) (w : W) :
    Degree r (fun x => L (v x) w) := by
  let B := EuclideanSpace.basisFun W ℂ
  let coord : State W →ₗ[ℂ] ℂ := (PiLp.projₗ 2 (fun _ : W => ℂ) w).comp L
  have expand (u : State W) : L u w = ∑ j, u j * coord (B j) := by
    change coord u = _
    simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr, smul_eq_mul, B] using
      congrArg coord (B.sum_repr u).symm
  simp_rw [expand]
  exact degree_sum Finset.univ _ fun j => by
    simpa only [Nat.add_zero] using degree_mul (hv j) (degree_const 0 (coord (B j)))

private theorem degree_run_from {r : ℕ} (c : List (Step W (Fin n) G O)) (a b : Fin n → G)
    (v : (Fin n → Bool) → State W) (hv : ∀ w, Degree r (fun x => v x w))
    (h : Hist c) (w : W) :
    Degree (queries c + r) (fun x => run c (fun i => if x i then b i else a i) (v x) h w) := by
  induction c generalizing r v with
  | nil => simpa [run, branchMap] using hv w
  | cons step rest ih =>
    cases step with
    | op op =>
      exact ih (fun x => op.kraus h.1 (v x)) (degree_linearMap _ v hv) h.2
    | query q =>
      let next (x : Fin n → Bool) := q.operator (fun i => if x i then b i else a i) (v x)
      have hn (j : W) : Degree (1 + r) (fun x => next x j) :=
        degree_mul (degree_single (q.address j)
          (fun z => q.phase j (if z then b (q.address j) else a (q.address j)))) (hv j)
      rw [queries_query, Nat.add_assoc]
      exact ih next hn h

/-- Each coordinate of the branch state has Boolean degree at most the query count. -/
theorem run_amplitude_degree (c : List (Step W (Fin n) G O)) (a b : Fin n → G)
    (v : State W) (h : Hist c) (w : W) :
    Degree (queries c) (fun x => run c (fun i => if x i then b i else a i) v h w) :=
  degree_run_from (r := 0) c a b (fun _ => v) (fun j => degree_const 0 (v j)) h w

private theorem degree_conj {r : ℕ} {f : (Fin n → Bool) → ℂ} (hf : Degree r f) :
    Degree r (fun x => conj (f x)) := by
  induction hf with
  | mono S z hS =>
    have heq (x : Fin n → Bool) :
        conj (if ∀ i ∈ S, x i = true then z else 0) =
          (if ∀ i ∈ S, x i = true then conj z else 0) := by split <;> simp
    change Degree r (fun x => conj (if ∀ i ∈ S, x i = true then z else 0))
    simp_rw [heq]
    exact Degree.mono S (conj z) hS
  | add _ _ ih₁ ih₂ => simpa only [map_add] using Degree.add ih₁ ih₂

/-- The complex embedding of a history's squared norm has degree at most twice the query count. -/
theorem run_norm_sq_degree (c : List (Step W (Fin n) G O)) (a b : Fin n → G)
    (v : State W) (h : Hist c) :
    Degree (2 * queries c)
      (fun x => ((‖run c (fun i => if x i then b i else a i) v h‖ ^ 2 : ℝ) : ℂ)) := by
  simp_rw [two_mul, EuclideanSpace.norm_sq_eq, Complex.ofReal_sum, Complex.ofReal_pow,
    ← Complex.mul_conj']
  exact degree_sum Finset.univ _ fun w =>
    degree_mul (run_amplitude_degree c a b v h w) (degree_conj (run_amplitude_degree c a b v h w))

/-- The joint probability that a transcript passes and all its selected coordinates are marked,
averaged over independent Bernoulli flags. Only passing transcripts must select exactly
`s` coordinates. The evaluation identity holds for every real parameter. -/
theorem marked_search_polynomial {s : ℕ} (c : List (Step W (Fin n) G O)) (a b : Fin n → G)
    (v : State W) (hv : ‖v‖ ^ 2 ≤ 1) (P : List O → Prop) (J : List O → Finset (Fin n))
    (hJ : ∀ l, P l → (J l).card = s) :
    ∃ f : ℝ[X], f.natDegree ≤ 2 * queries c + s ∧ X ^ s ∣ f ∧
      (∀ p : ℝ, f.eval p = ∑ x : Fin n → Bool, (∏ i, if x i then p else 1 - p) *
        eventMass c (fun i => if x i then b i else a i) v
          (fun l => P l ∧ ∀ i ∈ J l, x i = true)) ∧
      ∀ p ∈ Set.Icc (0 : ℝ) 1, f.eval p ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  let input (x : Fin n → Bool) (i : Fin n) := if x i then b i else a i
  let weight (p : ℝ) (x : Fin n → Bool) := ∏ i, if x i then p else 1 - p
  let pass (x : Fin n → Bool) (l : List O) := P l ∧ ∀ i ∈ J l, x i = true
  let mass (x : Fin n → Bool) (h : Hist c) :=
    @ite ℝ (pass x (claims c h)) (Classical.propDecidable _) (‖run c (input x) v h‖ ^ 2) 0
  have perHistory (h : Hist c) : ∃ f : ℝ[X], f.natDegree ≤ 2 * queries c + s ∧ X ^ s ∣ f ∧
      ∀ p, f.eval p = ∑ x, weight p x * mass x h := by
    by_cases hp : P (claims c h)
    · simpa only [hJ _ hp, Complex.ofReal_re, mass, pass, hp, true_and, weight, input] using
        tested_polynomial (run_norm_sq_degree c a b v h) (J (claims c h))
    · exact ⟨0, by simp, dvd_zero _, by simp [mass, pass, hp]⟩
  choose f hd hdiv he using perHistory
  have formula (p : ℝ) : (∑ h, f h).eval p = ∑ x, weight p x * eventMass c (input x) v (pass x) := by
    change (∑ h, f h).eval p = ∑ x, weight p x * ∑ h, mass x h
    simp only [eval_finsetSum, he, Finset.mul_sum]
    exact Finset.sum_comm
  refine ⟨∑ h, f h, natDegree_sum_le_of_forall_le _ _ (fun h _ => hd h),
    Finset.dvd_sum (fun h _ => hdiv h), formula, ?_⟩
  intro p hp
  have hw (x) : 0 ≤ weight p x :=
    Finset.prod_nonneg fun i _ => by cases x i <;> simp [hp.1, sub_nonneg.mpr hp.2]
  rw [formula]
  constructor
  · exact Finset.sum_nonneg fun x _ => mul_nonneg (hw x)
      (Finset.sum_nonneg fun h _ => show 0 ≤ mass x h by dsimp [mass]; split <;> positivity)
  · calc
      _ ≤ ∑ x, weight p x * 1 := Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left ((eventMass_le_norm_sq c (input x) v (pass x)).trans hv) (hw x)
      _ = 1 := by simpa [weight] using marked_mass (∅ : Finset (Fin n)) p

end QuantumNoiseStability.TimeSpace
end
end

-- Solutions.SortingPolynomial
section
namespace QNoiseStab.Supplement

open Polynomial Real

/-- Extrapolate from the Chebyshev interval to `cosh t`. -/
private theorem abs_eval_cosh_le {Q : ℝ[X]} {D : ℕ} (hdeg : Q.natDegree ≤ D)
    (hb : ∀ x ∈ Set.Icc (-1) 1, |Q.eval x| ≤ 1) (t : ℝ) :
    |Q.eval (cosh t)| ≤ cosh (D * t) := by
  have upper (R : ℝ[X]) (hd : R.natDegree ≤ D)
      (h : ∀ x ∈ Set.Icc (-1) 1, |R.eval x| ≤ 1) :
      R.eval (cosh t) ≤ cosh (D * t) := by
    simpa [Chebyshev.T_real_cosh] using
      (Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
        (k := 0) (one_le_cosh t) (degree_le_of_natDegree_le hd) h)
  apply abs_le.mpr
  constructor
  · have hn := upper (-Q) (by simpa using hdeg) (by simpa using hb)
    simpa using neg_le_neg hn
  · exact upper Q hdeg hb

/-- For a polynomial bounded by one on `[0,1]`, a factor `X ^ s` gives
the endpoint bound with absolute constant six throughout the interval.

For `p ≤ 1/4`, set `t = s / D` and `a = t² / 12`. The affine map
`x ↦ p + (cosh t - x) / 4` sends `[-1,1]` into `[a,1]`, where the
quotient by `X ^ s` is bounded by `1 / a ^ s`. Chebyshev extrapolation
to `x = cosh t` increases this bound by at most `cosh s ≤ 3 ^ s`. -/
theorem polynomial_endpoint_bound {P : ℝ[X]} {D s : ℕ}
    (hb : ∀ r ∈ Set.Icc 0 1, |P.eval r| ≤ 1) (hdeg : P.natDegree ≤ D)
    (hroot : X ^ s ∣ P) (hs : 0 < s) (hsD : s ≤ D)
    {p : ℝ} (hp : p ∈ Set.Icc 0 1) :
    |P.eval p| ≤ (6 * (D : ℝ) * sqrt p / s) ^ (2 * s) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hD : (0 : ℝ) < D := by exact_mod_cast hs.trans_le hsD
  have hsD' : (s : ℝ) ≤ D := by exact_mod_cast hsD
  have hsq := Real.sq_sqrt hp.1
  by_cases hsmall : p ≤ 1 / 4
  · by_cases hz : P = 0
    · simp [hz]
      positivity
    obtain ⟨Q, hQ⟩ := hroot
    have hdQ : Q.natDegree ≤ D :=
      (natDegree_le_of_dvd (show Q ∣ P from ⟨X ^ s, by rwa [mul_comm]⟩) hz).trans hdeg
    let t : ℝ := s / D
    have ht : 0 < t := div_pos hs' hD
    have ht1 : t ≤ 1 := (div_le_one hD).mpr hsD'
    have hc : cosh t ≤ 2 := by
      rw [cosh_eq]
      have h₁ := (Real.exp_le_exp.mpr ht1).trans Real.exp_one_lt_three.le
      have h₂ : exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    have hgap : t ^ 2 ≤ 3 * (cosh t - 1) := by
      have h := pow_le_pow_left₀ ht.le (Real.self_le_sinh_iff.mpr ht.le) 2
      nlinarith [Real.sinh_sq t, mul_nonneg (sub_nonneg.mpr (one_le_cosh t)) (sub_nonneg.mpr hc)]
    let a := t ^ 2 / 12
    have ha : 0 < a := by dsimp [a]; positivity
    let L : ℝ[X] := C (p + cosh t / 4) - C (1 / 4) * X
    have hL (x : ℝ) : L.eval x = p + cosh t / 4 - x / 4 := by simp [L]; ring
    let R := C (a ^ s) * Q.comp L
    have heval (x : ℝ) : |R.eval x| = a ^ s * |Q.eval (L.eval x)| := by
      simp [R, eval_comp, abs_mul, abs_of_nonneg ha.le]
    have hR : R.natDegree ≤ D := by
      have hlin : L.natDegree ≤ 1 := by
        apply natDegree_sub_le_of_le (m := 1) (n := 1)
        · simp
        · simp
      calc
        R.natDegree ≤ (Q.comp L).natDegree := natDegree_C_mul_le ..
        _ ≤ Q.natDegree * L.natDegree := natDegree_comp_le
        _ ≤ D * 1 := Nat.mul_le_mul hdQ hlin
        _ = D := Nat.mul_one _
    have hRb (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) : |R.eval x| ≤ 1 := by
      have hl : a ≤ L.eval x := by rw [hL]; dsimp [a]; linarith [hp.1, hx.2]
      have hu : L.eval x ≤ 1 := by rw [hL]; linarith [hx.1]
      have h := hb (L.eval x) ⟨ha.le.trans hl, hu⟩
      rw [hQ, eval_mul, eval_pow, eval_X, abs_mul, abs_pow, abs_of_nonneg (ha.le.trans hl)] at h
      rw [heval]
      exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le hl s) (abs_nonneg _)).trans h
    have h := abs_eval_cosh_le hR hRb t
    rw [heval, hL, show p + cosh t / 4 - cosh t / 4 = p by ring] at h
    have hDt : (D : ℝ) * t = s := by dsimp [t]; field_simp
    have hgrowth : cosh (D * t) ≤ (3 : ℝ) ^ s := by
      rw [hDt, cosh_eq]
      have he : exp (s : ℝ) ≤ (3 : ℝ) ^ s := by
        calc
          exp (s : ℝ) = exp 1 ^ s := by simp
          _ ≤ (3 : ℝ) ^ s := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le s
      have hn : exp (-(s : ℝ)) ≤ exp s := Real.exp_le_exp.mpr (by linarith)
      linarith
    have hquot : |Q.eval p| ≤ (3 / a) ^ s := by
      rw [div_pow, le_div_iff₀ (pow_pos ha s), mul_comm]
      exact h.trans hgrowth
    rw [hQ, eval_mul, eval_pow, eval_X, abs_mul, abs_pow, abs_of_nonneg hp.1]
    calc
      p ^ s * |Q.eval p| ≤ p ^ s * (3 / a) ^ s :=
        mul_le_mul_of_nonneg_left hquot (pow_nonneg hp.1 s)
      _ = (6 * (D : ℝ) * sqrt p / s) ^ (2 * s) := by
        rw [← mul_pow, pow_mul]
        congr 1
        dsimp [a, t]
        field_simp
        nlinarith only [hsq]
  · apply (hb p hp).trans
    apply one_le_pow₀
    apply (le_div_iff₀ hs').mpr
    have hhalf : 1 / 2 ≤ sqrt p := by nlinarith [Real.sqrt_nonneg p]
    nlinarith [mul_le_mul_of_nonneg_left hhalf hD.le]

/-- A single absolute constant works for all degrees and multiplicities. -/
theorem exists_polynomial_endpoint_bound :
    ∃ C : ℝ, 0 < C ∧ C ≤ 64 ∧ ∀ (P : ℝ[X]) (D s : ℕ),
      (∀ r ∈ Set.Icc 0 1, |P.eval r| ≤ 1) → P.natDegree ≤ D →
      X ^ s ∣ P → 0 < s → s ≤ D → ∀ p ∈ Set.Icc (0 : ℝ) 1,
      |P.eval p| ≤ (C * D * sqrt p / s) ^ (2 * s) := by
  exact ⟨6, by norm_num, by norm_num, fun _ _ _ hb hd hr hs hsD _ hp =>
    polynomial_endpoint_bound hb hd hr hs hsD hp⟩

end QNoiseStab.Supplement
end

-- Solutions.SortingRare
section
/-! Many reported positions cannot all contain letters from a rare set after few queries. -/

namespace QNoiseStab.Supplement

open QuantumNoiseStability.TimeSpace Finset
open scoped BigOperators Classical

variable {n s : ℕ} {W G O : Type} [Fintype W] [Fintype G] [DecidableEq G] [Nonempty G]

/-- A search bound for a uniform alphabet and an arbitrary output-dependent
selection of positions. The cost depends on the number of queries and the
density of the letters in the set. -/
theorem uniform_marked_search (hs : 0 < s) (c : List (Step W (Fin n) G O))
    (v : State W) (hv : ‖v‖ ^ 2 ≤ 1) (P : List O → Prop) (J : List O → Finset (Fin n))
    (hJ : ∀ l, P l → (J l).card = s) (B : Finset G) :
    success c v (fun x l => P l ∧ ∀ i ∈ J l, x i ∈ B) ≤
      (6 * ((2 * queries c + s : ℕ) : ℝ) * Real.sqrt (B.card / (Fintype.card G : ℝ)) / s) ^
        (2 * s) := by
  classical
  by_cases hB : B.Nonempty
  · by_cases htop : B = univ
    · rw [htop]
      have hG : 0 < (Fintype.card G : ℝ) := by positivity
      simp only [card_univ, div_self hG.ne', Real.sqrt_one, mul_one]
      apply (success_le_one c v hv _).trans
      apply one_le_pow₀
      rw [one_le_div (by positivity : 0 < (s : ℝ))]
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) (queries c), Nat.cast_nonneg (α := ℝ) s]
    · have : Nonempty {x // x ∈ B} := hB.to_subtype
      have : Nonempty {x // x ∉ B} := by
        obtain ⟨x, hx⟩ := not_forall.mp (mt eq_univ_of_forall htop)
        exact ⟨x, hx⟩
      let E (x : Fin n → G) := eventMass c x v (fun l => P l ∧ ∀ i ∈ J l, x i ∈ B)
      change (Fintype.card (Fin n → G) : ℝ)⁻¹ * ∑ x, E x ≤ _
      rw [← div_eq_inv_mul, ← Fintype.expect_eq_sum_div_card, expect_mixtureInput B hB htop E]
      apply Finset.expect_le univ_nonempty
      intro a _
      apply Finset.expect_le univ_nonempty
      intro b _
      obtain ⟨f, hdegree, hroot, heval, hb⟩ := marked_search_polynomial c (fun i => (a i).val)
        (fun i => (b i).val) v hv P J hJ
      let p : ℝ := B.card / Fintype.card G
      have hp : p ∈ Set.Icc 0 1 := ⟨by dsimp [p]; positivity, (div_le_one (by positivity)).mpr
        (by exact_mod_cast B.card_le_univ)⟩
      have hbound (r) (hr : r ∈ Set.Icc (0 : ℝ) 1) : |f.eval r| ≤ 1 := by
        rw [abs_of_nonneg (hb r hr).1]
        exact (hb r hr).2
      have h := polynomial_endpoint_bound hbound hdegree hroot hs (by omega) hp
      rw [abs_of_nonneg (hb p hp).1, heval] at h
      have hE (t : Fin n → Bool) : E (mixtureInput B a b t) =
          eventMass c (fun i => if t i then (b i).val else (a i).val) v
            (fun l => P l ∧ ∀ i ∈ J l, t i = true) := by
        simp only [E, mixtureInput_mem_iff]
        rfl
      simpa only [hE, mixtureFlagWeight, p] using h
  · rw [not_nonempty_iff_eq_empty.mp hB]
    have hz (x : Fin n → G) (l : List O) :
        ¬ (P l ∧ ∀ i ∈ J l, x i ∈ (∅ : Finset G)) := by
      rintro ⟨hl, hx⟩
      have hn : (J l).Nonempty := card_pos.mp ((hJ l hl).symm ▸ hs)
      obtain ⟨i, hi⟩ := hn
      exact notMem_empty _ (hx i hi)
    simp only [success, eventMass, hz, ite_false, sum_const_zero, mul_zero]
    positivity

end QNoiseStab.Supplement
end

-- Solutions.SortingSlice
section
/-! Success probability of a short sorting computation. -/

namespace QNoiseStab.Supplement

open QuantumNoiseStability QuantumNoiseStability.TimeSpace
open Finset Filter

private theorem sorting_short_of_scales {n m k Δ t s r : ℕ} (hm : n ^ 2 ≤ m) (hk : 4 ≤ k)
    (h : SortingSliceScales 6 n k Δ t s) (hs : 0 < s) (hsr : s ≤ r)
    {W : Type} [Fintype W] (c : List (Step W (Fin n) (Fin m) (Fin n × (Fin m × Fin n))))
    (v : State W) (hv : ‖v‖ ^ 2 ≤ 1) (ht : queries c ≤ t) :
    success c v (fun x => ShortSuccess r (sortFun x)) ≤ (2 : ℝ) ^ (-((k : ℝ) / 8)) := by
  classical
  have hkΔ := h.le_spacing
  have hΔn := h.spacing_le
  have hnm := (Nat.le_self_pow (by decide : 2 ≠ 0) n).trans hm
  have hΔ : 0 < Δ := by omega
  have : NeZero m := ⟨by omega⟩
  let wide := fun (x : Fin n → Fin m) (l : SortingClaims n m) =>
    CorrectOn (sortingOutput l) x ∧ WidelyClaimed Δ k l
  let bins := univ.filter fun B : Finset (Fin Δ) => B.card ≤ 2 * k
  let letters := fun B : Finset (Fin Δ) => univ.filter fun a : Fin m => sortingBin hΔ a ∈ B
  let rare := fun (B : Finset (Fin Δ)) (x : Fin n → Fin m) (l : SortingClaims n m) =>
    s ≤ (coords l).card ∧ ∀ i ∈ selectedClaims s l, x i ∈ letters B
  have hcover := success_cover_le bins c v (fun x => ShortSuccess r (sortFun x)) wide rare (by
    intro x l hl
    rcases sorting_claims_dichotomy (k := k) hΔ x l ⟨hsr.trans hl.1, hl.2⟩ with
      hw | ⟨B, hB, hc, hletters⟩
    · exact Or.inl hw
    · exact Or.inr ⟨B, mem_filter.mpr ⟨mem_univ _, hB⟩, hc,
        fun i hi => mem_filter.mpr ⟨mem_univ _, hletters i hi⟩⟩)
  let p := 16 * (Δ : ℝ) / n
  have hp : 0 < p := h.noise_pos
  have hp1 : p < 1 := h.noise_le_half.trans_lt (by norm_num)
  have hw : success c v wide ≤ ((1 - p) ^ t)⁻¹ *
      (Real.exp (-2 * (Δ : ℝ)) + (2 : ℝ) ^ (2 - (k : ℝ))) := by
    apply (measured_success_le_noise c v hv wide univ hp hp1
      (β := (2 : ℝ) ^ (2 - (k : ℝ))) (by positivity) ?_).trans
    · apply mul_le_mul _ (le_add_of_nonneg_left (Real.exp_pos _).le) (by positivity)
        (inv_nonneg.mpr (pow_nonneg (by linarith) _))
      simp only [← inv_pow]
      exact pow_le_pow_right₀ ((one_le_inv₀ (by linarith : 0 < 1 - p)).mpr (by linarith)) ht
    · intro l x hx
      obtain ⟨hc, hw⟩ := hx
      obtain ⟨I, hI, hcard, hsep⟩ := widelyClaimed_spacedOn hw
      simpa only [eventInputs, wide, hw, and_true, Noise.kernel_eq_site] using
        widelySpaced_noiseKernel_le hm hk hkΔ hΔn (p := p) le_rfl hp1.le hI hcard hsep hc
  let bound := (6 * (2 * (t : ℝ) + s) * Real.sqrt (4 * (k : ℝ) / Δ) / s) ^ (2 * s)
  have hrare (B : Finset (Fin Δ)) (hB : B ∈ bins) : success c v (rare B) ≤ bound := by
    apply (uniform_marked_search hs c v hv (fun l => s ≤ (coords l).card) (selectedClaims s)
      (fun _ hl => (selectedClaims_spec hl).2) (letters B)).trans
    have hd := sortingBin_density_le (m := m) hΔ (by omega) B (mem_filter.mp hB).2
    dsimp only [bound, letters]
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    gcongr
  have hcount : (bins.card : ℝ) ≤ (Δ : ℝ) ^ (2 * k + 1) := by
    exact_mod_cast sortingBin_cover_count_le (Δ := Δ) (by omega) k
  have hr : (∑ B ∈ bins, success c v (rare B)) ≤ (2 : ℝ) ^ (-(k : ℝ)) := calc
    _ ≤ ∑ _B ∈ bins, bound := sum_le_sum hrare
    _ = bins.card * bound := by simp
    _ ≤ (Δ : ℝ) ^ (2 * k + 1) * bound :=
      mul_le_mul_of_nonneg_right hcount (by dsimp [bound]; positivity)
    _ ≤ _ := h.rare
  exact hcover.trans ((add_le_add hw hr).trans h.combined)

/-- A sorting segment with the prescribed query budget produces eight times the rounded
logarithmic factor times `k` correct outputs with probability at most `2 ^ (-k / 8)`. -/
theorem sorting_short_success :
    ∀ᶠ n : ℕ in atTop, ∀ (m k : ℕ), n ^ 2 ≤ m → 4 ≤ k →
      (k : ℝ) * (8 * (sortingLogFactor n : ℝ)) ^ 3 ≤ (1 / 512 : ℝ) * n →
      ∀ (W : Type) [Fintype W]
        (c : List (Step W (Fin n) (Fin m) (Fin n × (Fin m × Fin n)))) (v : State W),
        ‖v‖ ^ 2 ≤ 1 → queries c ≤ sortingSegmentLength (1 / 512) k n →
        success c v (fun x => ShortSuccess (8 * sortingLogFactor n * k) (sortFun x)) ≤
          (2 : ℝ) ^ (-((1 / 8 : ℝ) * k)) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [sorting_slice_parameters 6 (by norm_num), hlog.eventually_gt_atTop 1]
    with n hparams hn m k hm hk hrange W _ c v hv ht
  have hL : 0 < sortingLogFactor n :=
    Nat.ceil_pos.mpr (div_pos (lt_trans zero_lt_one hn) (Real.log_pos hn))
  have h := hparams k hk hrange
  have hwidth : 4 * k * sortingLogFactor n ≤ 8 * sortingLogFactor n * k := by
    rw [mul_right_comm 8]
    gcongr
    norm_num
  simpa only [one_div_mul_eq_div] using
    sorting_short_of_scales hm hk h (by positivity) hwidth c v hv
      (by simpa only [sortingSegmentLength, mul_assoc] using ht)

end QNoiseStab.Supplement
end

-- Solutions.SortingRecovery
section
namespace QNoiseStab.Supplement

open QuantumNoiseStability TimeSpace

private theorem recovery_base_bound {m : ℕ} (hm : 2 ≤ m) :
    (2 * (m : ℝ) - 2) ^ 5 * (3 / (2 * m)) ^ 15 < (m : ℝ)⁻¹ := by
  rcases eq_or_lt_of_le hm with h | h
  · subst m
    norm_num
  -- For m ≥ 3, replacing 2m - 2 by 2m leaves the inequality 3^15 < 2^10 m^9.
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast (show 3 ≤ m by omega)
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hm3 9
  calc
    _ ≤ (2 * (m : ℝ)) ^ 5 * (3 / (2 * m)) ^ 15 := by
      gcongr <;> linarith
    _ = 3 ^ 15 / (2 ^ 10 * (m : ℝ) ^ 9) / m := by field_simp
    _ < _ := by
      rw [inv_eq_one_div, div_lt_div_iff_of_pos_right (by positivity),
        div_lt_iff₀ (by positivity)]
      linarith

/-- At this resampling rate the single-symbol agreement probability is exactly `3/(2m)`. -/
private theorem recovery_noise_parameter {n m t : ℕ} (hn : 0 < n) (hm : 2 ≤ m) (ht : 3 * t ≤ n) :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧
      ((1 - p) ^ t)⁻¹ * (1 - p + p / m) ^ n < (m : ℝ) ^ (-(n : ℝ) / 15) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : 0 < 2 * (m : ℝ) - 2 := by linarith
  let p := 1 - (2 * (m : ℝ) - 2)⁻¹
  have hq : 1 - p = (2 * (m : ℝ) - 2)⁻¹ := sub_sub_cancel _ _
  have hrow : 1 - p + p / m = 3 / (2 * m) := by
    dsimp [p]
    generalize hd : 2 * (m : ℝ) - 2 = d at *
    field_simp [hpos.ne', (by positivity : (m : ℝ) ≠ 0)]
    rw [← hd]
    ring
  refine ⟨p, sub_pos.mpr ((inv_lt_one₀ hpos).mpr (by linarith)),
    sub_lt_self _ (inv_pos.mpr hpos), ?_⟩
  rw [hrow, hq, inv_pow, inv_inv]
  apply lt_of_pow_lt_pow_left₀ 15 (Real.rpow_nonneg (by positivity) _)
  calc
    _ = (2 * (m : ℝ) - 2) ^ (t * 15) * ((3 / (2 * m)) ^ 15) ^ n := by
      rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm n 15]
    _ ≤ (2 * (m : ℝ) - 2) ^ (5 * n) * ((3 / (2 * m)) ^ 15) ^ n := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) (by omega))
        (by positivity)
    _ = ((2 * (m : ℝ) - 2) ^ 5 * (3 / (2 * m)) ^ 15) ^ n := by rw [mul_pow, pow_mul]
    _ < ((m : ℝ)⁻¹) ^ n := pow_lt_pow_left₀ (recovery_base_bound hm) (by positivity) hn.ne'
    _ = ((m : ℝ) ^ (-(n : ℝ) / 15)) ^ 15 := by
      rw [← Real.rpow_mul_natCast (by positivity), inv_pow, ← Real.rpow_natCast,
        ← Real.rpow_neg (by positivity)]
      congr 1
      push_cast
      ring

/-- Proposition 3.7 for sorting. A correct transcript specifies every input value. -/
theorem sorting_input_recovery {n m : ℕ} [NeZero m] {W : Type} [Fintype W]
    (l : List (Step W (Fin n) (Fin m) (Fin n × (Fin m × Fin n)))) (v : State W)
    (hv : ‖v‖ ^ 2 ≤ 1) (hn : 0 < n) (hm : 2 ≤ m) (ht : 3 * queries l ≤ n) :
    success l v (fun x => FullSuccess (sortFun x)) < (m : ℝ) ^ (-(n : ℝ) / 15) := by
  classical
  obtain ⟨p, hp0, hp1, hbound⟩ := recovery_noise_parameter hn hm ht
  apply lt_of_le_of_lt (measured_success_le_noise l v hv _ Finset.univ hp0 hp1
    (β := (1 - p + p / m) ^ n) (by positivity) ?_) hbound
  intro out x hx
  have he : eventInputs (fun y => FullSuccess (sortFun y)) out = {x} := by
    ext y
    rw [mem_eventInputs, Finset.mem_singleton]
    constructor
    · intro hy
      funext i
      obtain ⟨value, hi⟩ := hx.1 i
      exact congrArg Prod.fst ((hy.2 (i, value) hi).trans (hx.2 (i, value) hi).symm)
    · rintro rfl
      exact hx
  simp [he, Noise.kernel_eq_hamming, Noise.hammingOn]

end QNoiseStab.Supplement
end

-- Paper.TimeSpace.BasisMass
section
namespace QuantumNoiseStability.TimeSpace

/-- Squared norms after a linear map, summed over a family of total squared norm at most one. -/
theorem map_sum_le_basis_sum {W J : Type} [Fintype W] [Fintype J]
    (L : EuclideanSpace ℂ W →ₗ[ℂ] EuclideanSpace ℂ W)
    (v : J → EuclideanSpace ℂ W) (hv : ∑ j, ‖v j‖ ^ 2 ≤ 1) :
    ∑ j, ‖L (v j)‖ ^ 2 ≤ ∑ w, ‖L ((EuclideanSpace.basisFun W ℂ) w)‖ ^ 2 := by
  classical
  let b := EuclideanSpace.basisFun W ℂ
  let total := ∑ w, ‖L (b w)‖ ^ 2
  have bound (u : EuclideanSpace ℂ W) : ‖L u‖ ^ 2 ≤ ‖u‖ ^ 2 * total := by
    have expand : L u = ∑ w, u w • L (b w) := by
      calc L u = L (∑ w, (b.repr u w) • b w) := congrArg L (b.sum_repr u).symm
           _ = _ := by simp [b]
    have tri : ‖L u‖ ≤ ∑ w, ‖u w‖ * ‖L (b w)‖ := by
      rw [expand]
      exact (norm_sum_le _ _).trans_eq (by simp [norm_smul])
    calc
      ‖L u‖ ^ 2 ≤ (∑ w, ‖u w‖ * ‖L (b w)‖) ^ 2 := by gcongr
      _ ≤ (∑ w, ‖u w‖ ^ 2) * total := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = _ := by rw [EuclideanSpace.norm_sq_eq]
  calc
    ∑ j, ‖L (v j)‖ ^ 2 ≤ ∑ j, ‖v j‖ ^ 2 * total := Finset.sum_le_sum fun j _ => bound _
    _ = (∑ j, ‖v j‖ ^ 2) * total := (Finset.sum_mul ..).symm
    _ ≤ 1 * total := mul_le_mul_of_nonneg_right hv (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := one_mul _

end QuantumNoiseStability.TimeSpace
end

-- Paper.TimeSpace.Slicing
section
/-!
# Slicing a quantum computation

A correct full transcript covers every output coordinate. If the computation has few
slices then at least one slice prints many distinct correct outputs. At each boundary
the input-dependent memory is a family of subnormalized states. Replacing the initial state by a sum over basis states costs one factor of the memory dimension per slice.

The list and history argument generalizes the earlier `GeneralHashing.Slicing` proof.
-/

noncomputable section

namespace QuantumNoiseStability.TimeSpace

open Finset
open scoped Classical

variable {W ι G Y : Type} {m : ℕ} [Fintype W]

private theorem sum_comm_rotate {α β γ M : Type*} [AddCommMonoid M] [Fintype α] [Fintype β]
    [Fintype γ] (F : α → β → γ → M) :
    ∑ x, ∑ y, ∑ z, F x y z = ∑ z, ∑ x, ∑ y, F x y z := by
  calc ∑ x, ∑ y, ∑ z, F x y z = ∑ x, ∑ z, ∑ y, F x y z := by
        apply Finset.sum_congr rfl
        intro x _
        exact Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ y, F x y z := Finset.sum_comm

/-! ## The slice event -/

/-- The event that some slice's own record satisfies the short event for `k`. -/
def SliceEvent (k : ℕ) (a : Fin m → Y) :
    (cs : List (List (Step W ι G (Fin m × Y)))) → Hist cs.flatten → Prop
  | [], _ => False
  | c :: cs, h =>
      ShortSuccess k a (claims c (histAppend c cs.flatten h).1) ∨
        SliceEvent k a cs (histAppend c cs.flatten h).2

/-- The records of the slices along a history. -/
def records : (cs : List (List (Step W ι G (Fin m × Y)))) → Hist cs.flatten → List (List (Fin m × Y))
  | [], _ => []
  | c :: cs, h =>
      claims c (histAppend c cs.flatten h).1 :: records cs (histAppend c cs.flatten h).2

theorem flatten_records : ∀ (cs : List (List (Step W ι G (Fin m × Y)))) (h : Hist cs.flatten),
    (records cs h).flatten = claims cs.flatten h
  | [], h => by
    show [] = claims [] h
    rfl
  | c :: cs, h => by
    show claims c _ ++ (records cs _).flatten = claims (c ++ cs.flatten) h
    rw [flatten_records cs, claims_append]

theorem length_records : ∀ (cs : List (List (Step W ι G (Fin m × Y)))) (h : Hist cs.flatten),
    (records cs h).length = cs.length
  | [], _ => rfl
  | c :: cs, h => by
    show (records cs _).length + 1 = cs.length + 1
    rw [length_records cs]

theorem sliceEvent_of_mem_records (k : ℕ) (a : Fin m → Y) :
    ∀ (cs : List (List (Step W ι G (Fin m × Y)))) (h : Hist cs.flatten),
      (∃ l ∈ records cs h, ShortSuccess k a l) → SliceEvent k a cs h
  | [], _, ⟨l, hl, _⟩ => by simp [records] at hl
  | c :: cs, h, ⟨l, hl, hs⟩ => by
    simp only [records, List.mem_cons] at hl
    show ShortSuccess k a (claims c _) ∨ SliceEvent k a cs _
    rcases hl with rfl | hl
    · exact Or.inl hs
    · exact Or.inr (sliceEvent_of_mem_records k a cs _ ⟨l, hl, hs⟩)

/-- **Pigeonhole.** A fully successful history with `m > |cs| (k - 1)` has a slice whose
own record has at least `k` distinct correct claims, hence satisfies the short event. -/
theorem sliceEvent_of_fullSuccess {k : ℕ} {a : Fin m → Y} (cs : List (List (Step W ι G (Fin m × Y))))
    (h : Hist cs.flatten) (hfull : FullSuccess a (claims cs.flatten h))
    (hm : cs.length * (k - 1) < m) : SliceEvent k a cs h := by
  apply sliceEvent_of_mem_records
  apply exists_shortSuccess_of_cover k a (records cs h) univ
  · intro c _
    rw [flatten_records]
    exact hfull.1 c
  · rw [flatten_records]
    exact hfull.2
  · rw [length_records, Finset.card_univ, Fintype.card_fin]
    exact hm


private theorem sum_run_le_basis {J : Type} [Fintype J]
    (l : List (Step W ι G (Fin m × Y))) (x : ι → G) (h : Hist l)
    (v : J → State W) (hv : ∑ j, ‖v j‖ ^ 2 ≤ 1) :
    ∑ j, ‖run l x (v j) h‖ ^ 2 ≤
      ∑ w, ‖run l x ((EuclideanSpace.basisFun W ℂ) w) h‖ ^ 2 :=
  map_sum_le_basis_sum (branchMap l x h) v hv

variable [Fintype ι] [DecidableEq ι] [Fintype G] [Nonempty G]

private theorem sum_basis_short_le
    (f : (ι → G) → Fin m → Y) {k t : ℕ} {β : ℝ}
    (hshort : ∀ c : List (Step W ι G (Fin m × Y)), queries c ≤ t → ∀ w : W,
      success c ((EuclideanSpace.basisFun W ℂ) w) (fun x => ShortSuccess k (f x)) ≤ β)
    (c : List (Step W ι G (Fin m × Y))) (hc : queries c ≤ t) :
    ∑ w, ∑ x, eventMass c x ((EuclideanSpace.basisFun W ℂ) w) (ShortSuccess k (f x)) ≤
      (Fintype.card W : ℝ) * (β * (Fintype.card (ι → G) : ℝ)) := by
  calc ∑ w, ∑ x, eventMass c x ((EuclideanSpace.basisFun W ℂ) w) (ShortSuccess k (f x))
      ≤ ∑ _w : W, β * (Fintype.card (ι → G) : ℝ) := by
        apply Finset.sum_le_sum
        intro w _
        have h := hshort c hc w
        unfold success at h
        rwa [← div_eq_inv_mul, div_le_iff₀ (by positivity)] at h
    _ = _ := by simp

private theorem sliceEvent_sum_le (f : (ι → G) → Fin m → Y) {k t : ℕ} {β : ℝ}
    (hshort : ∀ c : List (Step W ι G (Fin m × Y)), queries c ≤ t → ∀ w : W,
      success c ((EuclideanSpace.basisFun W ℂ) w) (fun x => ShortSuccess k (f x)) ≤ β) :
    ∀ (cs : List (List (Step W ι G (Fin m × Y)))), (∀ c ∈ cs, queries c ≤ t) →
      ∀ {J : Type} [Fintype J] (ψ : J → (ι → G) → State W), (∀ x, ∑ j, ‖ψ j x‖ ^ 2 ≤ 1) →
      ∑ x, ∑ j, ∑ h : Hist cs.flatten,
        (if SliceEvent k (f x) cs h then ‖run cs.flatten x (ψ j x) h‖ ^ 2 else 0) ≤
        (cs.length : ℝ) * ((Fintype.card W : ℝ) * (β * (Fintype.card (ι → G) : ℝ)))
  | [], _, J, _, ψ, _ => by
    simp [SliceEvent]
  | c :: cs, hcs, J, _, ψ, hψ => by
    have hc : queries c ≤ t := hcs c List.mem_cons_self
    have hcs' : ∀ c' ∈ cs, queries c' ≤ t := fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')
    set F := cs.flatten with hF
    show ∑ x, ∑ j, ∑ h : Hist (c ++ F),
        (if SliceEvent k (f x) (c :: cs) h then ‖run (c ++ F) x (ψ j x) h‖ ^ 2
          else 0) ≤ _
    -- split every history of `c ++ F` into its `c` part and its `F` part
    have hsplit : ∀ x j, ∑ h : Hist (c ++ F),
        (if SliceEvent k (f x) (c :: cs) h then ‖run (c ++ F) x (ψ j x) h‖ ^ 2
          else 0) =
        ∑ h₁ : Hist c, ∑ h₂ : Hist F,
          (if ShortSuccess k (f x) (claims c h₁) ∨ SliceEvent k (f x) cs h₂ then
            ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0) := by
      intro x j
      rw [sum_hist_append c F]
      apply Finset.sum_congr rfl
      intro h₁ _
      apply Finset.sum_congr rfl
      intro h₂ _
      have e1 : histAppend c F ((histAppend c F).symm (h₁, h₂)) = (h₁, h₂) :=
        (histAppend c F).apply_symm_apply _
      have hev : SliceEvent k (f x) (c :: cs) ((histAppend c F).symm (h₁, h₂)) ↔
          ShortSuccess k (f x) (claims c h₁) ∨ SliceEvent k (f x) cs h₂ := by
        show ShortSuccess k (f x) (claims c (histAppend c F _).1) ∨
          SliceEvent k (f x) cs (histAppend c F _).2 ↔ _
        rw [e1]
      rw [run_append c F, e1]
      simp only [hev]
    simp_rw [hsplit]
    -- union bound
    have hunion : ∀ x j h₁ h₂,
        (if ShortSuccess k (f x) (claims c h₁) ∨ SliceEvent k (f x) cs h₂ then
          ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0) ≤
        (if ShortSuccess k (f x) (claims c h₁) then
          ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0) +
        (if SliceEvent k (f x) cs h₂ then
          ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0) := by
      intro x j h₁ h₂
      have h0 := sq_nonneg ‖run F x (run c x (ψ j x) h₁) h₂‖
      split_ifs <;> first | linarith | (exfalso; tauto)
    -- the first-slice term
    have hA : ∑ x, ∑ j, ∑ h₁ : Hist c, ∑ h₂ : Hist F,
        (if ShortSuccess k (f x) (claims c h₁) then
          ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0) ≤
        (Fintype.card W : ℝ) * (β * (Fintype.card (ι → G) : ℝ)) := by
      calc ∑ x, ∑ j, ∑ h₁ : Hist c, ∑ h₂ : Hist F,
            (if ShortSuccess k (f x) (claims c h₁) then
              ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0)
          ≤ ∑ x, ∑ j, ∑ h₁ : Hist c,
            (if ShortSuccess k (f x) (claims c h₁) then
              ‖run c x (ψ j x) h₁‖ ^ 2 else 0) := by
            gcongr with x _ j _ h₁ _
            split_ifs
            · exact sum_mass_run_le F x _
            · simp
        _ = ∑ x, ∑ h₁ : Hist c, ∑ j,
            (if ShortSuccess k (f x) (claims c h₁) then
              ‖run c x (ψ j x) h₁‖ ^ 2 else 0) := by
            exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ ≤ ∑ x, ∑ h₁ : Hist c, ∑ w : W,
            (if ShortSuccess k (f x) (claims c h₁) then
              ‖run c x ((EuclideanSpace.basisFun W ℂ) w) h₁‖ ^ 2 else 0) := by
            apply Finset.sum_le_sum
            intro x _
            apply Finset.sum_le_sum
            intro h₁ _
            by_cases he : ShortSuccess k (f x) (claims c h₁)
            · simpa only [if_pos he] using sum_run_le_basis c x h₁ (fun j => ψ j x) (hψ x)
            · simp [he]
        _ = ∑ w, ∑ x, eventMass c x ((EuclideanSpace.basisFun W ℂ) w) (ShortSuccess k (f x)) :=
            sum_comm_rotate _
        _ ≤ (Fintype.card W : ℝ) * (β * (Fintype.card (ι → G) : ℝ)) :=
            sum_basis_short_le f hshort c hc
    -- the remaining slices, by the induction hypothesis with the new starting family
    have hB : ∑ x, ∑ j, ∑ h₁ : Hist c, ∑ h₂ : Hist F,
        (if SliceEvent k (f x) cs h₂ then
          ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0) ≤
        (cs.length : ℝ) * ((Fintype.card W : ℝ) * (β * (Fintype.card (ι → G) : ℝ))) := by
      have hψ' : ∀ x, ∑ p : J × Hist c, ‖run c x (ψ p.1 x) p.2‖ ^ 2 ≤ 1 := by
        intro x
        rw [Fintype.sum_prod_type]
        calc ∑ j, ∑ h₁ : Hist c, ‖run c x (ψ j x) h₁‖ ^ 2
            ≤ ∑ j, ‖ψ j x‖ ^ 2 := Finset.sum_le_sum fun j _ => sum_mass_run_le c x _
          _ ≤ 1 := hψ x
      have := sliceEvent_sum_le f hshort cs hcs' (fun p : J × Hist c => fun x =>
        run c x (ψ p.1 x) p.2) hψ'
      simp_rw [Fintype.sum_prod_type] at this
      exact this
    calc ∑ x, ∑ j, ∑ h₁ : Hist c, ∑ h₂ : Hist F,
          (if ShortSuccess k (f x) (claims c h₁) ∨ SliceEvent k (f x) cs h₂ then
            ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0)
        ≤ ∑ x, ∑ j, ∑ h₁ : Hist c, ∑ h₂ : Hist F,
          ((if ShortSuccess k (f x) (claims c h₁) then
            ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0) +
          (if SliceEvent k (f x) cs h₂ then
            ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0)) := by
          gcongr with x _ j _ h₁ _ h₂ _
          exact hunion x j h₁ h₂
      _ = (∑ x, ∑ j, ∑ h₁ : Hist c, ∑ h₂ : Hist F,
          (if ShortSuccess k (f x) (claims c h₁) then
            ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0)) +
          (∑ x, ∑ j, ∑ h₁ : Hist c, ∑ h₂ : Hist F,
          (if SliceEvent k (f x) cs h₂ then
            ‖run F x (run c x (ψ j x) h₁) h₂‖ ^ 2 else 0)) := by
          simp_rw [Finset.sum_add_distrib]
      _ ≤ (Fintype.card W : ℝ) * (β * (Fintype.card (ι → G) : ℝ)) +
          (cs.length : ℝ) * ((Fintype.card W : ℝ) * (β * (Fintype.card (ι → G) : ℝ))) :=
          add_le_add hA hB
      _ = ((c :: cs).length : ℝ) *
          ((Fintype.card W : ℝ) * (β * (Fintype.card (ι → G) : ℝ))) := by
          rw [List.length_cons]
          push_cast
          ring


/-- If each short computation from an input-independent basis state succeeds with
probability at most `β`, a full computation that needs one such successful slice
has success probability at most the number of slices times `2 ^ S * β`. -/
theorem success_le_slices (f : (ι → G) → Fin m → Y)
    (l : List (Step W ι G (Fin m × Y))) (v : State W) (hv : ‖v‖ ^ 2 ≤ 1)
    {t k S : ℕ} {β : ℝ} (ht : 0 < t) (hβ : 0 ≤ β) (hmem : Fintype.card W ≤ 2 ^ S)
    (hshort : ∀ c : List (Step W ι G (Fin m × Y)), queries c ≤ t → ∀ w : W,
      success c ((EuclideanSpace.basisFun W ℂ) w) (fun x => ShortSuccess k (f x)) ≤ β)
    (hcount : sliceCount (queries l) t * (k - 1) < m) :
    success l v (fun x => FullSuccess (f x)) ≤ (sliceCount (queries l) t : ℝ) * (2 : ℝ)^S * β := by
  obtain ⟨cs, rfl, hcs, hlen⟩ := exists_chunks t ht l
  have hm := (Nat.mul_le_mul_right (k - 1) hlen).trans_lt hcount
  have hmain := sliceEvent_sum_le f hshort cs hcs (J := Unit) (fun _ _ => v) (fun _ => by simpa using hv)
  simp only [Finset.univ_unique, Finset.sum_singleton] at hmain
  have hfull : ∑ x, eventMass cs.flatten x v (FullSuccess (f x)) ≤
      (cs.length : ℝ) * ((Fintype.card W : ℝ) * (β * (Fintype.card (ι → G) : ℝ))) := by
    refine le_trans ?_ hmain
    apply Finset.sum_le_sum
    intro x _
    unfold eventMass
    apply Finset.sum_le_sum
    intro h _
    by_cases hf : FullSuccess (f x) (claims cs.flatten h)
    · simp [hf, sliceEvent_of_fullSuccess cs h hf hm]
    · simp only [if_neg hf]
      split_ifs <;> positivity
  have hN : (0 : ℝ) < Fintype.card (ι → G) := by positivity
  have hdim : (Fintype.card W : ℝ) ≤ (2 : ℝ) ^ S := by exact_mod_cast hmem
  have hlen' : (cs.length : ℝ) ≤ sliceCount (queries cs.flatten) t := by exact_mod_cast hlen
  unfold success
  rw [← div_eq_inv_mul, div_le_iff₀ hN]
  calc ∑ x, eventMass cs.flatten x v (FullSuccess (f x))
      ≤ (cs.length : ℝ) * ((Fintype.card W : ℝ) * (β * (Fintype.card (ι → G) : ℝ))) := hfull
    _ ≤ (sliceCount (queries cs.flatten) t : ℝ) *
          ((2 : ℝ) ^ S * (β * (Fintype.card (ι → G) : ℝ))) := by gcongr
    _ = _ := by ring

end QuantumNoiseStability.TimeSpace
end
end

-- Paper.TimeSpace.SitePreparation
section
noncomputable section

namespace QNoiseStab.Supplement.SiteExecution

open QuantumNoiseStability QuantumNoiseStability.TimeSpace

variable {M I G O : Type} [Fintype M] [DecidableEq M]

private def prepareBranch (L : Matrix M M ℂ) (w j : M) : State M →ₗ[ℂ] State M where
  toFun v := WithLp.toLp 2 (fun i => L i j * v w)
  map_add' u v := by ext i; exact mul_add _ _ _
  map_smul' c v := by ext i; exact mul_left_comm _ _ _

/-- Prepare the columns of a density matrix factor from the basis state at `w`. -/
def prepare {M O : Type} [Fintype M] [DecidableEq M] (L : Matrix M M ℂ) (w : M)
    (hL : ∑ j, ∑ i, ‖L i j‖ ^ 2 = 1) : TimeSpace.Instrument M O where
  outcomes := Fintype.card M
  kraus k := prepareBranch L w ((Fintype.equivFin M).symm k)
  emit _ := []
  subnormalized v := by
    rw [Equiv.sum_comp (Fintype.equivFin M).symm (fun j => ‖prepareBranch L w j v‖ ^ 2)]
    simp only [EuclideanSpace.norm_sq_eq]
    change (∑ j, ∑ i, ‖L i j * v w‖ ^ 2) ≤ ∑ i, ‖v i‖ ^ 2
    simp only [norm_mul, mul_pow, ← Finset.sum_mul, hL, one_mul]
    exact Finset.single_le_sum (fun i _ => sq_nonneg ‖v i‖) (Finset.mem_univ w)

/-- Summing over the silent preparation outcome runs the remaining steps on each column. -/
theorem sum_prepare (L : Matrix M M ℂ) (w : M) (hL : ∑ j, ∑ i, ‖L i j‖ ^ 2 = 1)
    (l : List (TimeSpace.Step M I G O)) (x : I → G) (g : List O → TimeSpace.State M → ℝ) :
    (∑ h : Hist (.op (prepare L w hL) :: l),
      g (claims _ h) (run _ x (EuclideanSpace.single w 1) h)) =
    ∑ j, ∑ h : Hist l, g (claims l h) (run l x (WithLp.toLp 2 (fun i => L i j)) h) := by
  change (∑ p : Fin (Fintype.card M) × Hist l, g (claims l p.2)
    (run l x (prepareBranch L w ((Fintype.equivFin M).symm p.1)
      (EuclideanSpace.single w 1)) p.2)) = _
  rw [Fintype.sum_prod_type, Equiv.sum_comp (Fintype.equivFin M).symm
    (fun j => ∑ h : Hist l, g (claims l h) (run l x (prepareBranch L w j
      (EuclideanSpace.single w 1)) h))]
  simp [prepareBranch]

end QNoiseStab.Supplement.SiteExecution
end
end

-- Solutions.MatrixMass
section
namespace QNoiseStab.Supplement.MatrixMass

open Matrix
open scoped ComplexOrder MatrixOrder

variable {I J : Type*} [Fintype I] [Fintype J]

theorem trace_mmstar_re (M : Matrix I J ℂ) :
    (M * Mᴴ).trace.re = ∑ j, ∑ i, ‖M i j‖ ^ 2 := by
  simp only [trace, diag_apply, mul_apply, conjTranspose_apply, Complex.star_def,
    Complex.re_sum, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  exact Finset.sum_comm

theorem posSemidef_factor {ρ : Matrix I I ℂ} (hρ : ρ.PosSemidef) :
    ∃ L : Matrix I I ℂ, ρ = L * Lᴴ := by
  classical
  exact CStarAlgebra.nonneg_iff_eq_mul_star_self.mp hρ.nonneg

theorem kraus_mass [DecidableEq I] (A : J → Matrix I I ℂ)
    (hA : ∑ j, (A j)ᴴ * A j = 1) (v : I → ℂ) :
    ∑ j, ∑ i, ‖(A j).mulVec v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  have h : ∑ j, star ((A j) *ᵥ v) ⬝ᵥ ((A j) *ᵥ v) = star v ⬝ᵥ v := calc
    _ = ∑ j, star v ⬝ᵥ (((A j)ᴴ * A j) *ᵥ v) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← mulVec_mulVec, dotProduct_mulVec (star v), star_mulVec]
    _ = star v ⬝ᵥ v := by rw [← dotProduct_sum, ← sum_mulVec, hA, one_mulVec]
  have re_star_mul (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  simpa only [dotProduct, Complex.re_sum, Pi.star_apply, re_star_mul] using congrArg Complex.re h

theorem trace_of_kraus_product (A : Matrix I I ℂ) {ρ : Matrix I I ℂ}
    (L : Matrix I J ℂ) (hρ : ρ = L * Lᴴ) :
    (A * ρ * Aᴴ).trace.re = ∑ j, ∑ i, ‖A.mulVec (fun k => L k j) i‖ ^ 2 := by
  have h : A * ρ * Aᴴ = (A * L) * (A * L)ᴴ := by
    simp only [hρ, conjTranspose_mul, Matrix.mul_assoc]
  rw [h, trace_mmstar_re]
  rfl

end QNoiseStab.Supplement.MatrixMass
end

-- Solutions.BranchExecution
section
namespace QNoiseStab.Supplement.BranchExecution

open Matrix

variable {J : Type*} [Fintype J] {T : ℕ}

/-- The final vector for one sequence of Kraus matrices, with an oracle between steps. -/
noncomputable def pathState (K : Fin (T + 1) → Matrix J J ℂ) (O : Matrix J J ℂ)
    (v : J → ℂ) : J → ℂ :=
  Fin.induction (motive := fun _ => J → ℂ) (K 0 *ᵥ v)
    (fun t w => K t.succ *ᵥ (O *ᵥ w)) (Fin.last T)

@[simp] theorem pathState_zero (K : Fin 1 → Matrix J J ℂ) (O : Matrix J J ℂ) (v : J → ℂ) :
    pathState K O v = K 0 *ᵥ v := rfl

private theorem induction_castSucc {S : Type*} (a : S) (step : Fin (T + 1) → S → S)
    (i : Fin (T + 1)) :
    Fin.induction (motive := fun _ => S) a step i.castSucc =
      Fin.induction (motive := fun _ => S) a (fun t => step t.castSucc) i := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih => exact congrArg (step i.castSucc) ih

private theorem induction_last_succ {S : Type*} (a : S) (step : Fin (T + 1) → S → S) :
    Fin.induction (motive := fun _ => S) a step (Fin.last (T + 1)) =
      step (Fin.last T)
        (Fin.induction (motive := fun _ => S) a (fun t => step t.castSucc) (Fin.last T)) :=
  congrArg (step (Fin.last T)) (induction_castSucc a step (Fin.last T))

theorem pathState_succ (K : Fin (T + 2) → Matrix J J ℂ) (O : Matrix J J ℂ) (v : J → ℂ) :
    pathState K O v =
      K (Fin.last (T + 1)) *ᵥ (O *ᵥ pathState (fun t => K t.castSucc) O v) :=
  induction_last_succ (K 0 *ᵥ v) (fun t w => K t.succ *ᵥ (O *ᵥ w))

variable {κ : Type*} [Fintype κ]

/-- Column `j` is the path starting from column `j` of the initial factor. -/
private noncomputable def pathMatrix (K : Fin (T + 1) → Matrix J J ℂ) (O L : Matrix J J ℂ) :
    Matrix J J ℂ :=
  of fun i j => pathState K O (fun k => L k j) i

private theorem pathMatrix_succ (K : Fin (T + 2) → Matrix J J ℂ) (O L : Matrix J J ℂ) :
    pathMatrix K O L =
      K (Fin.last (T + 1)) * (O * pathMatrix (fun t => K t.castSucc) O L) := by
  ext i j
  exact congrFun (pathState_succ K O (fun k => L k j)) i

private noncomputable def applyKraus (K : κ → Matrix J J ℂ) (ρ : Matrix J J ℂ) :
    Matrix J J ℂ := ∑ r, K r * ρ * (K r)ᴴ

private noncomputable def density (K : Fin (T + 1) → κ → Matrix J J ℂ) (O ρ : Matrix J J ℂ) :
    Matrix J J ℂ :=
  Fin.induction (motive := fun _ => Matrix J J ℂ) (applyKraus (K 0) ρ)
    (fun t σ => applyKraus (K t.succ) (O * σ * Oᴴ)) (Fin.last T)

private theorem density_eq_sum (K : Fin (T + 1) → κ → Matrix J J ℂ) (O L : Matrix J J ℂ) :
    density K O (L * Lᴴ) = ∑ r : Fin (T + 1) → κ,
      let M := pathMatrix (fun t => K t (r t)) O L
      M * Mᴴ := by
  classical
  induction T with
  | zero =>
    change (∑ r, K 0 r * (L * Lᴴ) * (K 0 r)ᴴ) = _
    apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) κ).symm
    intro r
    change K 0 r * (L * Lᴴ) * (K 0 r)ᴴ = (K 0 r * L) * (K 0 r * L)ᴴ
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  | succ T ih =>
    unfold density
    rw [induction_last_succ]
    change applyKraus (K (Fin.last (T + 1)))
      (O * density (fun t => K t.castSucc) O (L * Lᴴ) * Oᴴ) = _
    rw [ih]
    simp only [applyKraus, Matrix.mul_sum, Matrix.sum_mul]
    rw [← Fintype.sum_prod_type']
    apply Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (T + 2) => κ))
    intro ⟨s, r⟩
    simp only [Fin.snocEquiv_apply, pathMatrix_succ, Fin.snoc_last, Fin.snoc_castSucc,
      conjTranspose_mul, Matrix.mul_assoc]

variable {n d : ℕ} {W : Type} [DecidableEq W]

/-- The published phase query on the full memory. -/
noncomputable abbrev oracle (ω : ℂ) (y : Fin n → ZMod d) :=
  Matrix.kronecker (QNoiseStab.phaseQuery ω y) (1 : Matrix W W ℂ)

local notation "Mem" => (Fin n × ZMod d) × W

variable [NeZero d] [Fintype W] {K V ι : Type} [Fintype K] [Fintype V] [Fintype ι]

/-- Every initial density matrix has a factor whose columns have total squared norm one. -/
theorem exists_start_factor (A : SpaceBoundedAlg n d W K V ι T) :
    ∃ L : Matrix Mem Mem ℂ, A.start = L * Lᴴ ∧ ∑ j, ∑ i, ‖L i j‖ ^ 2 = 1 := by
  obtain ⟨L, hL⟩ := MatrixMass.posSemidef_factor A.start_psd
  refine ⟨L, hL, ?_⟩
  rw [← MatrixMass.trace_mmstar_re, ← hL, A.start_trace, Complex.one_re]

/-- Sum the squared final amplitudes over Kraus paths and columns of the initial factor. -/
theorem commitProb_eq_sum (A : SpaceBoundedAlg n d W K V ι T) (ω : ℂ) (y : Fin n → ZMod d)
    (o : Fin (T + 1) → Option (K × V)) (L : Matrix Mem Mem ℂ)
    (hL : A.start = L * Lᴴ) :
    A.commitProb ω y o = ∑ r : Fin (T + 1) → ι, ∑ j : Mem, ∑ i : Mem,
      ‖pathState (fun t => (A.step t).kraus (o t) (r t)) (oracle ω y) (fun k => L k j) i‖ ^ 2 := by
  change (density (fun t => (A.step t).kraus (o t)) (oracle ω y) A.start).trace.re = _
  rw [hL, density_eq_sum, trace_sum, Complex.re_sum]
  exact Finset.sum_congr rfl fun r _ => MatrixMass.trace_mmstar_re _

open Classical in
/-- Average the path expansion over inputs and sum over correct commit sequences. -/
theorem successProb_eq_sum {X Y : Type} [Fintype X] (A : SpaceBoundedAlg n d W K V ι T)
    (enc : X ≃ ZMod d) (ω : ℂ) (q : V → Y) (f : (Fin n → X) → K → Y)
    (L : Matrix Mem Mem ℂ) (hL : A.start = L * Lᴴ) :
    A.successProb enc ω q f = ((Fintype.card X : ℝ) ^ n)⁻¹ *
      ∑ x : Fin n → X, ∑ o : Fin (T + 1) → Option (K × V),
        if CommitsCorrect q (f x) o then
          ∑ r : Fin (T + 1) → ι, ∑ j : Mem, ∑ i : Mem,
            ‖pathState (fun t => (A.step t).kraus (o t) (r t))
              (oracle ω (fun k => enc (x k))) (fun k => L k j) i‖ ^ 2
        else 0 := by
  simp only [SpaceBoundedAlg.successProb, commitProb_eq_sum A ω _ _ L hL]

end QNoiseStab.Supplement.BranchExecution
end

-- Paper.TimeSpace.SiteRuns
section
/-! Simulation of the site oracle and instruments with a chronological output tape. -/

noncomputable section

namespace QNoiseStab.Supplement.SiteExecution

open QuantumNoiseStability QuantumNoiseStability.TimeSpace Matrix
open scoped Classical

variable {K V Y X W κ : Type} {n d T : ℕ}

/-- Each commit emits its coordinate and decoded value. -/
def record (q : V → Y) (o : Option (K × V)) : List (K × Y) :=
  (o.map (fun p => (p.1, q p.2))).toList

/-- The records in instrument order, including repeated commits. -/
def transcript {k : ℕ} (q : V → Y) (o : Fin k → Option (K × V)) : List (K × Y) :=
  (List.ofFn o).flatMap (record q)

private theorem mem_record (q : V → Y) (j : K) (b : Y) (o : Option (K × V)) :
    (j, b) ∈ record q o ↔ ∃ v, o = some (j, v) ∧ b = q v := by
  cases o with
  | none => simp [record]
  | some p =>
    rcases p with ⟨k, v⟩
    simp [record, eq_comm (a := k), @eq_comm V v]

private theorem mem_transcript {k : ℕ} (q : V → Y) (o : Fin k → Option (K × V))
    (j : K) (b : Y) :
    (j, b) ∈ transcript q o ↔ ∃ t v, o t = some (j, v) ∧ b = q v := by
  simp [transcript, List.mem_flatMap, List.mem_ofFn, mem_record]

theorem fullSuccess_transcript (q : V → Y) (z : K → Y) (o : Fin (T + 1) → Option (K × V)) :
    TimeSpace.FullSuccess z (transcript q o) ↔ CommitsCorrect q z o := by
  constructor
  · rintro ⟨cover, agree⟩
    refine ⟨fun t j v h => (agree (j, q v) ((mem_transcript ..).2 ⟨t, v, h, rfl⟩)).symm, ?_⟩
    intro j
    obtain ⟨b, h⟩ := cover j
    obtain ⟨t, v, h, _⟩ := (mem_transcript ..).1 h
    exact ⟨t, v, h⟩
  · rintro ⟨agree, cover⟩
    constructor
    · intro j
      obtain ⟨t, v, h⟩ := cover j
      exact ⟨q v, (mem_transcript ..).2 ⟨t, v, h, rfl⟩⟩
    · rintro ⟨j, b⟩ h
      obtain ⟨t, v, ho, hb⟩ := (mem_transcript ..).1 h
      exact (agree t j v ho).symm.trans hb.symm

local notation "Mem" => (Fin n × ZMod d) × W
local notation "Branch" => Option (K × V) × κ
local notation "Inst" => KAQROM.Instrument (Option (K × V)) Mem Mem κ

variable [NeZero d] (enc : X ≃ ZMod d) (ω : ℂ) (hω : ω ^ d = 1)

/-- The phase uses the encoded symbol at the address in the query register. -/
def siteQuery : PhaseQuery Mem (Fin n) X where
  address w := w.1.1
  phase w a := ω ^ (w.1.2 * enc a).val
  norm_phase w a := by
    have hroot : ‖ω‖ = 1 :=
      (pow_eq_one_iff_of_nonneg (norm_nonneg ω) (NeZero.ne d)).mp
        (by simpa only [norm_pow, norm_one] using congrArg norm hω)
    simp [norm_pow, hroot]

variable [Fintype W] [DecidableEq W]

theorem siteQuery_apply (x : Fin n → X) (v : TimeSpace.State Mem) :
    (siteQuery enc ω hω).operator x v =
      WithLp.toLp 2 ((BranchExecution.oracle ω (enc ∘ x)) *ᵥ v.ofLp) := by
  ext w
  unfold BranchExecution.oracle phaseQuery Matrix.kronecker
  rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal]
  simp [Matrix.mulVec_diagonal, siteQuery]

variable [Fintype K] [Fintype V] [Fintype κ] (q : V → Y)

private def measure (I : Inst) : TimeSpace.Instrument Mem (K × Y) where
  outcomes := Fintype.card Branch
  kraus j := let b := (Fintype.equivFin Branch).symm j
             (I.kraus b.1 b.2).toEuclideanLin
  emit j := record q ((Fintype.equivFin Branch).symm j).1
  subnormalized v := by
    let A (b : Branch) := I.kraus b.1 b.2
    have hc : ∑ b, (A b)ᴴ * A b = 1 := by
      rw [Fintype.sum_prod_type]
      exact I.complete
    change (∑ j, ‖(A ((Fintype.equivFin Branch).symm j)).toEuclideanLin v‖ ^ 2) ≤ ‖v‖ ^ 2
    rw [Equiv.sum_comp (Fintype.equivFin Branch).symm (fun b => ‖(A b).toEuclideanLin v‖ ^ 2)]
    simp_rw [EuclideanSpace.norm_sq_eq]
    exact (MatrixMass.kraus_mass A hc v.ofLp).le

/-- The initial instrument is followed by one query and one instrument at every later time. -/
def compiledSteps : {T : ℕ} → (I : Fin (T + 1) → Inst) → List (TimeSpace.Step Mem (Fin n) X (K × Y))
  | 0, I => [.op (measure q (I 0))]
  | T + 1, I => compiledSteps (fun i => I i.castSucc) ++
      [.query (siteQuery enc ω hω), .op (measure q (I (Fin.last (T + 1))))]

theorem queries_compiledSteps (I : Fin (T + 1) → Inst) :
    queries (compiledSteps enc ω hω q I) = T := by
  induction T with
  | zero => rfl
  | succ T ih => simp [compiledSteps, queries_append, ih]

private theorem sum_measure (I : Inst) (x : Fin n → X) (v : TimeSpace.State Mem)
    (g : List (K × Y) → TimeSpace.State Mem → ℝ) :
    (∑ h, g (claims [.op (measure q I)] h) (run [.op (measure q I)] x v h)) =
      ∑ b : Branch, g (record q b.1) (WithLp.toLp 2 ((I.kraus b.1 b.2) *ᵥ v.ofLp)) := by
  let f (b : Branch) := g (record q b.1) (WithLp.toLp 2 ((I.kraus b.1 b.2) *ᵥ v.ofLp))
  change (∑ h : Fin (Fintype.card Branch) × Unit,
    g (record q ((Fintype.equivFin Branch).symm h.1).1 ++ claims [] h.2) _) = ∑ b, f b
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_unique, claims, List.append_nil]
  exact Equiv.sum_comp (Fintype.equivFin Branch).symm f

private theorem sum_last (a : List (TimeSpace.Step Mem (Fin n) X (K × Y))) (I : Inst)
    (x : Fin n → X) (v : TimeSpace.State Mem) (g : List (K × Y) → TimeSpace.State Mem → ℝ) :
    let tail := [.query (siteQuery enc ω hω), .op (measure q I)]
    (∑ h, g (claims (a ++ tail) h) (run (a ++ tail) x v h)) =
      ∑ b : Branch, ∑ h, g (claims a h ++ record q b.1)
        (WithLp.toLp 2 ((I.kraus b.1 b.2) *ᵥ
          (BranchExecution.oracle ω (enc ∘ x) *ᵥ (run a x v h).ofLp))) := by
  dsimp only
  rw [sum_hist_append]
  simp only [claims_append, run_append, Equiv.apply_symm_apply]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  change (∑ k, g (claims a h ++ claims [.op (measure q I)] k)
    (run [.op (measure q I)] x ((siteQuery enc ω hω).operator x (run a x v h)) k)) = _
  rw [siteQuery_apply]
  exact sum_measure q I x _ (fun l w => g (claims a h ++ l) w)

/-- Sum a function of the chronological transcript and final state over instrument branches. -/
theorem sum_compiledSteps (I : Fin (T + 1) → Inst) (x : Fin n → X) (v : TimeSpace.State Mem)
    (g : List (K × Y) → TimeSpace.State Mem → ℝ) :
    (∑ h, g (claims (compiledSteps enc ω hω q I) h) (run (compiledSteps enc ω hω q I) x v h)) =
      ∑ p : Fin (T + 1) → Branch, g (transcript q (fun t => (p t).1))
        (WithLp.toLp 2 (BranchExecution.pathState (fun t => (I t).kraus (p t).1 (p t).2)
          (BranchExecution.oracle ω (enc ∘ x)) v.ofLp)) := by
  induction T generalizing g with
  | zero =>
    rw [compiledSteps, sum_measure]
    apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) Branch).symm
    intro b
    simp [transcript, Equiv.funUnique, Equiv.piUnique]
  | succ T ih =>
    rw [compiledSteps, sum_last]
    have hpre (b : Branch) := ih (fun i => I i.castSucc)
      (fun l w => g (l ++ record q b.1)
        (WithLp.toLp 2 ((I (Fin.last (T + 1))).kraus b.1 b.2 *ᵥ
          (BranchExecution.oracle ω (enc ∘ x) *ᵥ w.ofLp))))
    simp_rw [hpre]
    rw [← Fintype.sum_prod_type']
    apply Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (T + 2) => Branch))
    rintro ⟨b, p⟩
    rw [BranchExecution.pathState_succ]
    simp only [Fin.snocEquiv_apply, Fin.snoc_last, Fin.snoc_castSucc]
    congr 1
    simp only [transcript, List.ofFn_succ' (n := T + 1), Fin.snoc_castSucc, Fin.snoc_last,
      List.concat_eq_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

end QNoiseStab.Supplement.SiteExecution
end
end

-- Solutions.SpaceAccounting
section
/-! Physical memory and the address register in the public instrument model. -/

namespace QNoiseStab.Supplement

/-- The trace-one start state requires at least one physical memory basis state. -/
theorem SpaceBoundedAlg.memory_nonempty {n d T : ℕ} [NeZero d] {W K V κ : Type}
    [Fintype W] [DecidableEq W] [Fintype K] [Fintype V] [Fintype κ]
    (A : SpaceBoundedAlg n d W K V κ T) : Nonempty ((Fin n × ZMod d) × W) := by
  by_contra h
  have : IsEmpty ((Fin n × ZMod d) × W) := ⟨fun w => h ⟨w⟩⟩
  simpa [Matrix.trace] using A.start_trace

/-- The address register must fit along with the phase register and the workspace. -/
theorem SpaceBoundedAlg.address_fits {n d T S : ℕ} [NeZero d] {W K V κ : Type}
    [Fintype W] [DecidableEq W] [Fintype K] [Fintype V] [Fintype κ]
    (A : SpaceBoundedAlg n d W K V κ T) (hA : A.FitsInSpace S) : n ≤ 2^S := by
  obtain ⟨⟨⟨_, _⟩, w⟩⟩ := A.memory_nonempty
  have : Nonempty W := ⟨w⟩
  have h₁ : n ≤ n*d := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne d))
  exact (h₁.trans (Nat.le_mul_of_pos_right _ Fintype.card_pos)).trans hA

theorem SpaceBoundedAlg.card_memory_le {n d T S : ℕ} [NeZero d] {W K V κ : Type}
    [Fintype W] [DecidableEq W] [Fintype K] [Fintype V] [Fintype κ]
    (A : SpaceBoundedAlg n d W K V κ T) (hA : A.FitsInSpace S) :
    Fintype.card ((Fin n × ZMod d) × W) ≤ 2^S := by
  simpa only [SpaceBoundedAlg.FitsInSpace, Fintype.card_prod, Fintype.card_fin, ZMod.card] using hA

end QNoiseStab.Supplement
end

-- Paper.TimeSpace.SiteExecution
section
/-! # Exact simulation of the published mixed-state query model on its original registers -/

noncomputable section

namespace QNoiseStab.Supplement.SiteExecution

open QuantumNoiseStability.TimeSpace
open BranchExecution
open scoped Classical

variable {n d T : ℕ} [NeZero d] {W K V κ X Y : Type}
  [Fintype W] [DecidableEq W] [Fintype K] [Fintype V] [Fintype κ]
local notation "Mem" => (Fin n × ZMod d) × W
local notation "Outcome" => Option (K × V)

variable (A : SpaceBoundedAlg n d W K V κ T) (enc : X ≃ ZMod d) (ω : ℂ) (hω : ω ^ d = 1)
  (q : V → Y)

/-- A silent first instrument prepares the public input-independent density matrix. -/
def programSteps : List (Step Mem (Fin n) X (K × Y)) :=
  let L : Matrix Mem Mem ℂ := (exists_start_factor A).choose
  .op (prepare L (Classical.choice A.memory_nonempty) (exists_start_factor A).choose_spec.2) ::
    compiledSteps enc ω hω q A.step

/-- The silent preparation starts from a fixed, normalized memory basis vector. -/
def initialVector : State Mem := EuclideanSpace.single (Classical.choice A.memory_nonempty) 1

theorem queries_programSteps : queries (programSteps A enc ω hω q) = T :=
  queries_compiledSteps enc ω hω q A.step

private theorem sum_pair_paths {O κ : Type} [Fintype O] [Fintype κ] {k : ℕ}
    (weight : (Fin k → O) → (Fin k → κ) → ℝ) :
    (∑ p : Fin k → O × κ, weight (fun t => (p t).1) (fun t => (p t).2)) =
      ∑ o, ∑ r, weight o r := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => O) (fun _ => κ))
    _ _ (fun _ => rfl)

/-- The two computations assign the same probability to a complete correct record on every input. -/
theorem eventMass_programSteps (x : Fin n → X) (z : K → Y) :
    eventMass (programSteps A enc ω hω q) x (initialVector A) (FullSuccess z) =
      ∑ o, if CommitsCorrect q z o then A.commitProb ω (enc ∘ x) o else 0 := by
  let L : Matrix Mem Mem ℂ := (exists_start_factor A).choose
  let w := Classical.choice A.memory_nonempty
  let l := compiledSteps enc ω hω q A.step
  let score := fun (c : List (K × Y)) (v : State Mem) => if FullSuccess z c then ‖v‖^2 else 0
  change (∑ h, score (claims (Step.op (prepare L w _) :: l) h)
    (run _ x (EuclideanSpace.single w 1) h)) = _
  rw [sum_prepare L w (exists_start_factor A).choose_spec.2 l x score]
  dsimp only [l]
  simp_rw [sum_compiledSteps enc ω hω q A.step x _ score]
  rw [Finset.sum_comm]
  let weight (o : Fin (T+1) → Outcome) (r : Fin (T+1) → κ) :=
    ∑ j, score (transcript q o) (WithLp.toLp 2
      (pathState (fun t => (A.step t).kraus (o t) (r t)) (oracle ω (enc ∘ x)) (fun i => L i j)))
  change (∑ p : Fin (T+1) → Outcome × κ, weight (fun t => (p t).1) (fun t => (p t).2)) = _
  rw [sum_pair_paths]
  apply Finset.sum_congr rfl
  intro o _
  by_cases hc : CommitsCorrect q z o <;>
    simp [weight, score, fullSuccess_transcript, hc, EuclideanSpace.norm_sq_eq,
      commitProb_eq_sum A ω _ o L (exists_start_factor A).choose_spec.1]

/-- Uniform success is preserved for every target, including targets with repeated values. -/
theorem success_programSteps [Fintype X] (f : (Fin n → X) → K → Y) :
    A.successProb enc ω q f = success (programSteps A enc ω hω q) (initialVector A)
      (fun x => FullSuccess (f x)) := by
  simp [SpaceBoundedAlg.successProb, success, eventMass_programSteps, Function.comp_def]

include hω in
/-- Every published algorithm gives a program with the same workspace and query count. -/
theorem exists_program [Fintype X] (f : (Fin n → X) → K → Y) :
    ∃ l : List (Step Mem (Fin n) X (K × Y)), ∃ v : State Mem,
      ‖v‖ ^ 2 ≤ 1 ∧ queries l = T ∧
        A.successProb enc ω q f ≤ success l v (fun x => FullSuccess (f x)) :=
  ⟨programSteps A enc ω hω q, initialVector A, by simp [initialVector], queries_programSteps A enc ω hω q,
    (success_programSteps A enc ω hω q f).le⟩

end QNoiseStab.Supplement.SiteExecution
end
end

-- Solutions.Theorem51
section
set_option autoImplicit false

namespace QNoiseStab.Supplement

open Filter Real QuantumNoiseStability.TimeSpace

/-- The sorting tradeoff for measured programs whose operations can each emit a list of claims. -/
theorem sorting_tradeoff_of_input_recovery :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n m : ℕ, ∀ [NeZero m], n₀ ≤ n → n ^ 2 ≤ m →
      ∀ (S : ℕ) (W : Type) [Fintype W], n ^ 2 ≤ 2 ^ S → Fintype.card W ≤ 2 ^ S →
      ∀ (l : List (Step W (Fin n) (Fin m) (Fin n × (Fin m × Fin n)))) (v : State W),
        ‖v‖ ^ 2 ≤ 1 →
        (2 : ℝ) ^ (-min (S : ℝ) (c * n * (Real.log (Real.log n) / Real.log n) ^ 3)) ≤
            success l v (fun x => FullSuccess (sortFun x)) →
        C * (n : ℝ) ^ ((4 : ℝ) / 3) * Real.log (Real.log n) /
            ((S : ℝ) ^ ((1 : ℝ) / 3) * Real.log n) ≤ queries l := by
  classical
  refine ⟨1 / 16, by norm_num, (1 / 512) / (64 * (24 : ℝ) ^ (1 / 3 : ℝ)), by positivity, ?_⟩
  have hgrowth : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨n₀, h₀⟩ := eventually_atTop.1
    ((sorting_short_success.and (hgrowth.eventually_ge_atTop 512)).and (eventually_ge_atTop 3))
  refine ⟨n₀, ?_⟩
  intro n m _ hn hm S W _ hreg hmem l v hv hsucc
  obtain ⟨⟨hslice, hroot⟩, hn3⟩ := h₀ n hn
  have hsize : 1 ≤ (1 / 512 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) := by
    change 512 ≤ (n : ℝ) ^ (1 / 3 : ℝ) at hroot
    linarith
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hlog : 1 < log (n : ℝ) :=
    (lt_log_iff_exp_lt (by linarith)).2 (exp_one_lt_three.trans_le hn')
  have hll := log_pos hlog
  have hratio : log (log (n : ℝ)) ≤ log n := by
    linarith [log_le_sub_one_of_pos (by linarith : 0 < log (n : ℝ))]
  have hu := (one_le_div hll).2 hratio
  have hcube : (log (log (n : ℝ)) / log n) ^ 3 ≤ 1 :=
    pow_le_one₀ (div_nonneg hll.le (by linarith)) ((div_le_one (by linarith)).2 hratio)
  have hcap : (1 / 16 : ℝ) * n * (log (log n) / log n) ^ 3 < n / 15 := by
    linarith [mul_le_mul_of_nonneg_left hcube (show 0 ≤ (1 / 16 : ℝ) * n by positivity)]
  have hS : 0 < S := by
    by_contra! h
    have : S = 0 := by omega
    simp [this] at hreg
    nlinarith
  have hmain := sorting_time_lower_bound (n := n) (m := m) (T := queries l)
    (A := 24) (α := 1 / 512) (γ := 1 / 8)
    (by omega) (by nlinarith) hS hreg (by decide) (by norm_num) (by norm_num) (by norm_num)
    hsize hu (min_le_left _ _) ((min_le_right _ _).trans_lt hcap) hsucc (fun ht =>
      (sorting_input_recovery l v hv (by omega) (by nlinarith) ht).le)
  apply le_trans _ (hmain ?_)
  · apply le_of_eq
    simp only [Nat.cast_ofNat, div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  · intro k hk hrange houtputs
    have hkpow : 1 ≤ (k : ℝ) ^ (2 / 3 : ℝ) :=
      one_le_rpow (by exact_mod_cast (by omega : 1 ≤ k)) (by norm_num)
    have ht : 0 < sortingSegmentLength (1 / 512) k n := by
      apply Nat.floor_pos.mpr
      calc
        (1 : ℝ) ≤ (1 / 512) * (n : ℝ) ^ (1 / 3 : ℝ) := hsize
        _ ≤ (1 / 512) * (n : ℝ) ^ (1 / 3 : ℝ) * (k : ℝ) ^ (2 / 3 : ℝ) :=
          le_mul_of_one_le_right (by positivity) hkpow
        _ = _ := by ring
    apply success_le_slices sortFun l v hv ht (by positivity) hmem _ houtputs
    intro c hc i
    have hi : ‖(EuclideanSpace.basisFun _ ℂ) i‖ ^ 2 ≤ 1 := by simp
    exact hslice m k hm hk hrange _ c _ hi hc

/-- **Theorem 5.1** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), p.26, restated p.31): "There is a constant c > 0 such that the
following holds. Let m ≥ n^2. For ℓ = min(S, cn(log log n/ log n)^3), any quantum query algorithm
using T queries and space S that sorts inputs in [m]^n with probability at least 2^{−ℓ} must have T
that is Ω(n^{4/3} log log n/(S^{1/3} log n))."

There are constants `c > 0` and `C > 0` and a threshold `n₀` such that for all `n ≥ n₀`,
`m ≥ n^2` and `S`, every `T`-query algorithm using at most `S` qubits that computes
`SORT_{n,[m]}` (every input index `i` committed with `(x_i, r_i)`, all commits correct) with
probability at least `2^{−ℓ}` on a uniform input in `[m]^n`, `ℓ = min(S, c·n·(log log n/log n)^3)`,
has `T ≥ C·n^{4/3}·log log n/(S^{1/3}·log n)`.

**Formalization Note** `log` is the natural logarithm (a change of base is absorbed by `c` and
`C`). `[m]` is `Fin m`, encoded into `ZMod m` by any bijection `enc`; the root `ω` is any `ω`
with `ω^m = 1`. `[NeZero m]` is needed for the phase register and only excludes `m = 0`, which
`m ≥ n^2` already excludes for `n ≥ 1`. Ω is the pair `C`, `n₀`, chosen after `c` and before
everything else. -/
private theorem submission_proof :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n m : ℕ, ∀ [NeZero m], n₀ ≤ n → n ^ 2 ≤ m →
      ∀ (S : ℕ) (W V κ : Type) [Fintype W] [DecidableEq W] [Fintype V] [Fintype κ] (T : ℕ)
        (A : SpaceBoundedAlg n m W (Fin n) V κ T) (q : V → Fin m × Fin n) (enc : Fin m ≃ ZMod m)
        (ω : ℂ), ω ^ m = 1 → A.FitsInSpace S →
        (2 : ℝ) ^ (-min (S : ℝ) (c * n * (Real.log (Real.log n) / Real.log n) ^ 3)) ≤
            A.successProb enc ω q sortFun →
        C * (n : ℝ) ^ ((4 : ℝ) / 3) * Real.log (Real.log n) /
            ((S : ℝ) ^ ((1 : ℝ) / 3) * Real.log n) ≤ T := by
  obtain ⟨c, hc, C, hC, n₀, bound⟩ := sorting_tradeoff_of_input_recovery
  refine ⟨c, hc, C, hC, n₀, ?_⟩
  intro n m _ hn hm S W V κ _ _ _ _ T A q enc ω hω hspace hsucc
  obtain ⟨⟨⟨i, _⟩, w⟩⟩ := A.memory_nonempty
  have : Nonempty W := ⟨w⟩
  have hreg : n ^ 2 ≤ 2 ^ S :=
    (hm.trans (Nat.le_mul_of_pos_left m (Nat.zero_lt_of_lt i.isLt))).trans
      ((Nat.le_mul_of_pos_right (n * m) Fintype.card_pos).trans hspace)
  obtain ⟨l, v, hv, hT, hsim⟩ := SiteExecution.exists_program A enc ω hω q sortFun
  simpa only [hT] using bound n m hn hm S _ hreg (A.card_memory_le hspace) l v hv (hsucc.trans hsim)

end QNoiseStab.Supplement
end

section
set_option autoImplicit false
open QNoiseStab QNoiseStab.Supplement

set_option linter.unusedVariables false in
theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n m : ℕ, ∀ [NeZero m], n₀ ≤ n → n ^ 2 ≤ m →
      ∀ (S : ℕ) (W V κ : Type) [Fintype W] [DecidableEq W] [Fintype V] [Fintype κ] (T : ℕ)
        (A : SpaceBoundedAlg n m W (Fin n) V κ T) (q : V → Fin m × Fin n) (enc : Fin m ≃ ZMod m)
        (ω : ℂ), ω ^ m = 1 → A.FitsInSpace S →
        (2 : ℝ) ^ (-min (S : ℝ) (c * n * (Real.log (Real.log n) / Real.log n) ^ 3)) ≤
            A.successProb enc ω q sortFun →
        C * (n : ℝ) ^ ((4 : ℝ) / 3) * Real.log (Real.log n) /
            ((S : ℝ) ^ ((1 : ℝ) / 3) * Real.log n) ≤ T :=
  @QNoiseStab.Supplement.submission_proof

end
