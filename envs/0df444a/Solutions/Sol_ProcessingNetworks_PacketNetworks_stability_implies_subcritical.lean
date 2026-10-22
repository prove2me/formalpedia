-- Prove2me | solution 1 for ProcessingNetworks.PacketNetworks.stability_implies_subcritical
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:27:28.985971+00:00
-- url     : https://prove2.me/submissions/323da0c3-af1e-48cf-9adf-27794d8515ca

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_MarkovianPolicy
import Definitions.Def_ProcessingNetworks_PacketNetworks_SubcriticalRegion



namespace ProcessingNetworks.PacketNetworks

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SIS

/-! ### Part A: a stationary distribution from positive recurrence at a single state. -/

section Stationary
variable {X : Type*} (jump : X → PMF X) (x0 : X)

/-- expected number of visits to `y` before returning to `x0`. -/
noncomputable def mu (y : X) : ℝ≥0∞ := ∑' n : ℕ, Stability.tabooProb jump x0 n y

noncomputable def Mtot : ℝ≥0∞ := ∑' y : X, mu jump x0 y

lemma mu_x0 (hrec : Stability.Recurrent jump x0) : mu jump x0 x0 = 1 := by
  unfold mu
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp [Stability.tabooProb]

lemma mu_invariant (hrec : Stability.Recurrent jump x0) (y : X) :
    ∑' z : X, mu jump x0 z * jump z y = mu jump x0 y := by
  unfold mu
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  by_cases hy : y = x0
  · subst hy
    have h1 : ∀ n, ∑' z, Stability.tabooProb jump y n z * jump z y = Stability.firstReturnProb jump y n :=
      fun n => rfl
    simp_rw [h1]
    rw [hrec]
    rw [tsum_eq_zero_add' ENNReal.summable]
    simp [Stability.tabooProb]
  · have h1 : ∀ n, ∑' z, Stability.tabooProb jump x0 n z * jump z y =
        Stability.tabooProb jump x0 (n+1) y := by
      intro n; simp [Stability.tabooProb, hy]
    simp_rw [h1]
    conv_rhs => rw [tsum_eq_zero_add' ENNReal.summable]
    simp [Stability.tabooProb, hy]

lemma Mtot_eq : Mtot jump x0 = Stability.meanReturnTime jump (fun _ => (1:ℝ)) x0 := by
  unfold Mtot mu Stability.meanReturnTime
  simp only [inv_one, ENNReal.ofReal_one, mul_one]
  exact ENNReal.tsum_comm

lemma Mtot_ne_zero (hrec : Stability.Recurrent jump x0) : Mtot jump x0 ≠ 0 := by
  intro h
  have : mu jump x0 x0 ≤ Mtot jump x0 := ENNReal.le_tsum x0
  rw [mu_x0 jump x0 hrec, h] at this
  simp at this

/-- the stationary distribution -/
noncomputable def pi (y : X) : ℝ≥0∞ := mu jump x0 y / Mtot jump x0

lemma pi_sum (hrec : Stability.Recurrent jump x0) (hfin : Mtot jump x0 ≠ ⊤) :
    ∑' y : X, pi jump x0 y = 1 := by
  unfold pi
  simp_rw [div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right, ← div_eq_mul_inv]
  exact ENNReal.div_self (Mtot_ne_zero jump x0 hrec) hfin

lemma pi_invariant (hrec : Stability.Recurrent jump x0) (y : X) :
    ∑' z : X, pi jump x0 z * jump z y = pi jump x0 y := by
  unfold pi
  simp_rw [div_eq_mul_inv, mul_right_comm _ (Mtot jump x0)⁻¹]
  rw [ENNReal.tsum_mul_right, mu_invariant jump x0 hrec]

lemma pi_x0_pos (hrec : Stability.Recurrent jump x0) (hfin : Mtot jump x0 ≠ ⊤) :
    0 < pi jump x0 x0 := by
  unfold pi
  rw [mu_x0 jump x0 hrec]
  exact ENNReal.div_pos one_ne_zero hfin

lemma pi_ne_top (hrec : Stability.Recurrent jump x0) (hfin : Mtot jump x0 ≠ ⊤) (y : X) :
    pi jump x0 y ≠ ⊤ := by
  have : pi jump x0 y ≤ 1 := by
    rw [← pi_sum jump x0 hrec hfin]; exact ENNReal.le_tsum y
  exact ne_top_of_le_ne_top ENNReal.one_ne_top this

/-- stationarity for arbitrary nonnegative test functions -/
lemma pi_stationary (hrec : Stability.Recurrent jump x0) (g : X → ℝ≥0∞) :
    ∑' z : X, pi jump x0 z * ∑' y : X, jump z y * g y = ∑' y : X, pi jump x0 y * g y := by
  simp_rw [← ENNReal.tsum_mul_left, ← mul_assoc]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_right, pi_invariant jump x0 hrec]

end Stationary

/-! ### Part B: kernel formulas. -/

section Kernel
variable {I J : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  (dat : PacketNetworkData I J) (P : PacketPrimitives I J Ω)

/-- the next state as a vector of naturals -/
def nxt (z e : Fin I → ℕ) (s : Fin J → ℕ) : Fin I → ℕ :=
  fun i => (nextState dat (fun i => (z i : ℤ)) e s i).toNat

lemma Rint_sum_le (z : Fin I → ℕ) (s : Fin J → ℕ)
    (hs : ∀ i, (B dat).mulVec (fun j => (s j : ℝ)) i ≤ z i) (i : Fin I) :
    ∑ j, Rint dat i j * (s j : ℤ) ≤ z i := by
  have h := hs i
  simp only [Matrix.mulVec, dotProduct, B] at h
  have h2 : (∑ j, Rint dat i j * (s j : ℤ) : ℝ) ≤ ∑ j, (if dat.u j = i then (1:ℝ) else 0) * (s j : ℝ) := by
    push_cast
    apply Finset.sum_le_sum
    intro j _
    simp only [Rint]
    push_cast
    have : (0:ℝ) ≤ s j := by positivity
    split_ifs <;> nlinarith
  have h3 : ((∑ j, Rint dat i j * (s j : ℤ) : ℤ) : ℝ) ≤ (z i : ℝ) := by
    push_cast at h2 ⊢; linarith
  exact_mod_cast h3

lemma nextState_nonneg (z e : Fin I → ℕ) (s : Fin J → ℕ)
    (hs : ∀ i, (B dat).mulVec (fun j => (s j : ℝ)) i ≤ z i) (i : Fin I) :
    (e i : ℤ) ≤ nextState dat (fun i => (z i : ℤ)) e s i := by
  simp only [nextState]
  have := Rint_sum_le dat z s hs i
  linarith

lemma cast_nxt (z e : Fin I → ℕ) (s : Fin J → ℕ)
    (hs : ∀ i, (B dat).mulVec (fun j => (s j : ℝ)) i ≤ z i) :
    (fun i => (nxt dat z e s i : ℤ)) = nextState dat (fun i => (z i : ℤ)) e s := by
  funext i
  simp only [nxt]
  have h1 := nextState_nonneg dat z e s hs i
  have h2 : (0:ℤ) ≤ e i := by positivity
  rw [Int.toNat_of_nonneg (le_trans h2 h1)]

lemma eq_nxt_iff (z e y : Fin I → ℕ) (s : Fin J → ℕ)
    (hs : ∀ i, (B dat).mulVec (fun j => (s j : ℝ)) i ≤ z i) :
    ((fun i => (y i : ℤ)) = nextState dat (fun i => (z i : ℤ)) e s) ↔ y = nxt dat z e s := by
  rw [← cast_nxt dat z e s hs]
  constructor
  · intro h; funext i; have := congrFun h i; simpa using this
  · intro h; subst h; rfl

lemma nxt_apply_eq (z e : Fin I → ℕ) (s : Fin J → ℕ)
    (hs : ∀ i, (B dat).mulVec (fun j => (s j : ℝ)) i ≤ z i) (i : Fin I) :
    (nxt dat z e s i : ℤ) + ∑ j, Rint dat i j * (s j : ℤ) = z i + e i := by
  have h := congrFun (cast_nxt dat z e s hs) i
  change (nxt dat z e s i : ℤ) = nextState dat (fun i => (z i : ℤ)) e s i at h
  rw [h]; simp only [nextState]; ring

/-- the arrival law -/
lemma tsum_prob_mul (hE : AEMeasurable (P.Eincr 1) ℙ) (ψ : (Fin I → ℕ) → ℝ≥0∞) :
    ∑' e, ℙ {ω | P.Eincr 1 ω = e} * ψ e = ∫⁻ ω, ψ (P.Eincr 1 ω) := by
  rw [← lintegral_map' (measurable_of_countable ψ).aemeasurable hE, lintegral_countable']
  congr 1; funext e
  rw [Measure.map_apply_of_aemeasurable hE (measurableSet_singleton e), mul_comm]
  rfl

lemma tsum_prob_eq_one (hE : AEMeasurable (P.Eincr 1) ℙ) :
    ∑' e, ℙ {ω | P.Eincr 1 ω = e} = 1 := by
  have := tsum_prob_mul P hE (fun _ => 1)
  simpa using this

lemma measurableSet_f_pre (hf : ∀ z, Measurable (P.f z)) (z : Fin I → ℕ) (T : Set (Fin J → ℕ)) :
    MeasurableSet ((P.f z) ⁻¹' T) :=
  hf z (Set.to_countable T).measurableSet

/-- the kernel formula -/
lemma jump_tsum (jump : (Fin I → ℕ) → PMF (Fin I → ℕ)) (hjump : IsPolicyChain dat P jump)
    (S : Finset (Fin J → ℕ)) (hadm : IsAdmissibleMarkovianPolicy dat S P.f)
    (hf : ∀ z, Measurable (P.f z)) (z : Fin I → ℕ) (φ : (Fin I → ℕ) → ℝ≥0∞) :
    ∑' y, jump z y * φ y =
      ∫⁻ u in Set.Ioo (0:ℝ) 1, ∑' e, ℙ {ω | P.Eincr 1 ω = e} * φ (nxt dat z e (P.f z u)) := by
  have hmeas : ∀ y, Measurable (fun u : ℝ => (∑' e : Fin I → ℕ,
      (if (fun i => (y i : ℤ)) = nextState dat (fun i => (z i : ℤ)) e (P.f z u) then
        ℙ {ω | P.Eincr 1 ω = e} else 0)) * φ y) := by
    intro y
    refine Measurable.mul_const ?_ _
    refine Measurable.tsum fun e => ?_
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_f_pre P hf z {s | (fun i => (y i : ℤ)) = nextState dat (fun i => (z i : ℤ)) e s}
  have hj : ∀ y, jump z y * φ y = ∫⁻ u in Set.Ioo (0:ℝ) 1, (∑' e : Fin I → ℕ,
      (if (fun i => (y i : ℤ)) = nextState dat (fun i => (z i : ℤ)) e (P.f z u) then
        ℙ {ω | P.Eincr 1 ω = e} else 0)) * φ y := by
    intro y
    rw [hjump z y]
    rw [← lintegral_mul_const _ (by
    refine Measurable.tsum fun e => ?_
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_f_pre P hf z {s | _ = nextState dat (fun i => (z i : ℤ)) e s})]
  simp_rw [hj]
  rw [← lintegral_tsum (fun y => (hmeas y).aemeasurable)]
  refine setLIntegral_congr_fun measurableSet_Ioo ?_
  intro u hu
  have hs := (hadm z u hu.1 hu.2).2
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  congr 1; funext e
  rw [tsum_eq_single (nxt dat z e (P.f z u))]
  · rw [if_pos ((eq_nxt_iff dat z e _ _ hs).2 rfl)]
  · intro y hy
    rw [if_neg (fun h => hy ((eq_nxt_iff dat z e _ _ hs).1 h)), zero_mul]

end Kernel

/-! ### Part C: the real test function and the balance identity. -/

/-- the truncated test-function increment -/
def Q (c : ℝ) (M : ℕ) (n zi : ℝ) : ℝ := min n M + c - min zi M

section Qlemmas
variable {c r e zi n : ℝ} {M M' : ℕ}

lemma Q_nonneg (hc : 0 ≤ c) (hr2 : r ≤ c) (he : 0 ≤ e) (hn : n = zi + e - r) :
    0 ≤ Q c M n zi := by
  unfold Q
  rcases le_total n M with h1 | h1 <;> rcases le_total zi M with h2 | h2 <;>
    simp only [min_eq_left, min_eq_right, h1, h2] <;> linarith

lemma Q_le (hr2 : r ≤ c) (he : 0 ≤ e) (hn : n = zi + e - r) (_hc : 0 ≤ c) :
    Q c M n zi ≤ (e - r + c) + (if (M : ℝ) < zi then c else 0) := by
  unfold Q
  split_ifs with h
  · rw [min_eq_right h.le]
    have : min n M ≤ M := min_le_right _ _
    linarith
  · push Not at h
    rw [min_eq_left h]
    have : min n M ≤ n := min_le_left _ _
    linarith

lemma Q_shift (hzM : zi ≤ M) (hn : n = zi + e - r) :
    Q c M n zi = min (e - r) (M - zi) + c := by
  unfold Q
  rw [min_eq_left hzM, hn]
  rcases le_total (zi + e - r) M with h | h
  · rw [min_eq_left h, min_eq_left (by linarith)]; ring
  · rw [min_eq_right h, min_eq_right (by linarith)]; ring

lemma Q_mono (hzM : zi ≤ M) (hMM : M ≤ M') : Q c M n zi ≤ Q c M' n zi := by
  unfold Q
  have hzM' : zi ≤ M' := le_trans hzM (by exact_mod_cast hMM)
  rw [min_eq_left hzM, min_eq_left hzM']
  have : min n M ≤ min n M' := min_le_min_left _ (by exact_mod_cast hMM)
  linarith

lemma iSup_ofReal_min (a c : ℝ) :
    ⨆ M : ℕ, ENNReal.ofReal (min a M + c) = ENNReal.ofReal (a + c) := by
  apply le_antisymm
  · exact iSup_le fun M => ENNReal.ofReal_le_ofReal (by linarith [min_le_left a (M:ℝ)])
  · refine le_iSup_of_le ⌈a⌉₊ ?_
    rw [min_eq_left (Nat.le_ceil a)]

end Qlemmas

section Analysis
variable {I J : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  (dat : PacketNetworkData I J) (P : PacketPrimitives I J Ω)
  (S : Finset (Fin J → ℕ)) (jump : (Fin I → ℕ) → PMF (Fin I → ℕ))

/-- probability of the arrival vector `e` -/
noncomputable def pe (e : Fin I → ℕ) : ℝ≥0∞ := ℙ {ω | P.Eincr 1 ω = e}

/-- the class-`i` net departure under the policy -/
noncomputable def rr (i : Fin I) (z : Fin I → ℕ) (u : ℝ) : ℝ := (R dat).mulVec (realize (P.f z u)) i

/-- a uniform bound on `|rr|` -/
noncomputable def cc (i : Fin I) : ℝ := ∑ s ∈ S, |(R dat).mulVec (realize s) i|

lemma cc_nonneg (i : Fin I) : 0 ≤ cc dat S i := Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma abs_le_cc (i : Fin I) {s : Fin J → ℕ} (hs : s ∈ S) :
    |(R dat).mulVec (realize s) i| ≤ cc dat S i :=
  Finset.single_le_sum (f := fun s => |(R dat).mulVec (realize s) i|) (fun _ _ => abs_nonneg _) hs

lemma Rsum_cast (s : Fin J → ℕ) (i : Fin I) :
    ((∑ j, Rint dat i j * (s j : ℤ) : ℤ) : ℝ) = (R dat).mulVec (realize s) i := by
  simp only [Matrix.mulVec, dotProduct, R, Rint, realize]
  push_cast
  rfl

lemma nxt_real (z e : Fin I → ℕ) (s : Fin J → ℕ)
    (hs : ∀ i, (B dat).mulVec (fun j => (s j : ℝ)) i ≤ z i) (i : Fin I) :
    (nxt dat z e s i : ℝ) = z i + e i - (R dat).mulVec (realize s) i := by
  have h := nxt_apply_eq dat z e s hs i
  have h2 : ((nxt dat z e s i : ℤ) : ℝ) + ((∑ j, Rint dat i j * (s j : ℤ) : ℤ) : ℝ) = (z i : ℝ) + e i := by
    exact_mod_cast h
  rw [Rsum_cast] at h2
  push_cast at h2
  linarith

noncomputable def Psi (c : ℝ) (i : Fin I) (M : ℕ) (z : Fin I → ℕ) : ℝ≥0∞ :=
  ∫⁻ u in Set.Ioo (0:ℝ) 1, ∑' e, pe P e * ENNReal.ofReal (Q c M (nxt dat z e (P.f z u) i) (z i))

noncomputable def Lam (i : Fin I) : ℝ≥0∞ := ∑' e, pe P e * (e i : ℝ≥0∞)

noncomputable def rhoE (c : ℝ) (i : Fin I) (z : Fin I → ℕ) : ℝ≥0∞ :=
  ∫⁻ u in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (c - rr dat P i z u)

noncomputable def psi (c : ℝ) (i : Fin I) (z : Fin I → ℕ) : ℝ≥0∞ := Lam P i + rhoE dat P c i z

lemma vol_Ioo01 : (volume : Measure ℝ) (Set.Ioo 0 1) = 1 := by
  rw [Real.volume_Ioo]; simp

lemma int_add_const (g : ℝ → ℝ≥0∞) (a : ℝ≥0∞) :
    ∫⁻ u in Set.Ioo (0:ℝ) 1, (g u + a) = (∫⁻ u in Set.Ioo (0:ℝ) 1, g u) + a := by
  rw [lintegral_add_right' _ aemeasurable_const, setLIntegral_const, vol_Ioo01, mul_one]

lemma int_const_add (g : ℝ → ℝ≥0∞) (a : ℝ≥0∞) :
    ∫⁻ u in Set.Ioo (0:ℝ) 1, (a + g u) = a + ∫⁻ u in Set.Ioo (0:ℝ) 1, g u := by
  rw [lintegral_add_left' aemeasurable_const, setLIntegral_const, vol_Ioo01, mul_one]

variable (hE : AEMeasurable (P.Eincr 1) ℙ)
include hE

lemma tsum_pe_add_const (h : (Fin I → ℕ) → ℝ≥0∞) (a : ℝ≥0∞) :
    ∑' e, pe P e * (h e + a) = (∑' e, pe P e * h e) + a := by
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
  unfold pe
  rw [tsum_prob_eq_one P hE, one_mul]

lemma tsum_pe_const_add (h : (Fin I → ℕ) → ℝ≥0∞) (a : ℝ≥0∞) :
    ∑' e, pe P e * (a + h e) = a + ∑' e, pe P e * h e := by
  simp_rw [add_comm a]
  rw [tsum_pe_add_const P hE, add_comm]

lemma tsum_pe_shift (c : ℝ) (i : Fin I) (r : ℝ) (hr : r ≤ c) :
    ∑' e, pe P e * ENNReal.ofReal ((e i : ℝ) - r + c) = Lam P i + ENNReal.ofReal (c - r) := by
  have : ∀ e : Fin I → ℕ, ENNReal.ofReal ((e i : ℝ) - r + c) = (e i : ℝ≥0∞) + ENNReal.ofReal (c - r) := by
    intro e
    rw [show (e i : ℝ) - r + c = (e i : ℝ) + (c - r) by ring,
      ENNReal.ofReal_add (Nat.cast_nonneg _) (by linarith), ENNReal.ofReal_natCast]
  simp_rw [this]
  rw [tsum_pe_add_const P hE]
  rfl

variable (hf : ∀ z, Measurable (P.f z))
include hf

omit hE in
lemma meas_comp (z : Fin I → ℕ) (G : (Fin J → ℕ) → ℝ≥0∞) : Measurable (fun u => G (P.f z u)) :=
  (measurable_of_countable G).comp (hf z)

variable (hadm : IsAdmissibleMarkovianPolicy dat S P.f)
include hadm

omit hE hf in
lemma rr_bounds (i : Fin I) (z : Fin I → ℕ) {u : ℝ} (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    -cc dat S i ≤ rr dat P i z u ∧ rr dat P i z u ≤ cc dat S i := by
  have := abs_le_cc dat S i (hadm z u hu.1 hu.2).1
  exact abs_le.1 this

/-- Claim 1: the kernel identity for the truncated test function. -/
lemma claim1 (hjump : IsPolicyChain dat P jump) (i : Fin I) (M : ℕ) (z : Fin I → ℕ) :
    (∑' y, jump z y * ENNReal.ofReal (min (y i : ℝ) M)) + ENNReal.ofReal (cc dat S i) =
      Psi dat P (cc dat S i) i M z + ENNReal.ofReal (min (z i : ℝ) M) := by
  rw [jump_tsum dat P jump hjump S hadm hf z, Psi, ← int_add_const, ← int_add_const]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun u hu => ?_)
  have hs := (hadm z u hu.1 hu.2).2
  obtain ⟨hr1, hr2⟩ := rr_bounds dat P S hadm i z hu
  change (∑' e, pe P e * ENNReal.ofReal (min _ _)) + _ = _
  rw [← tsum_pe_add_const P hE, ← tsum_pe_add_const P hE]
  congr 1; funext e; congr 1
  rw [← ENNReal.ofReal_add (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (cc_nonneg dat S i),
    ← ENNReal.ofReal_add (Q_nonneg (cc_nonneg dat S i) hr2 (Nat.cast_nonneg (e i))
      (nxt_real dat z e _ hs i)) (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  congr 1; unfold Q; ring

/-- Claim 2: stationarity gives `∑ π Ψ_M = c`. -/
lemma claim2 (hjump : IsPolicyChain dat P jump) (hrec : Stability.Recurrent jump 0)
    (hfin : Mtot jump 0 ≠ ⊤) (i : Fin I) (M : ℕ) :
    ∑' z, pi jump 0 z * Psi dat P (cc dat S i) i M z = ENNReal.ofReal (cc dat S i) := by
  set g : (Fin I → ℕ) → ℝ≥0∞ := fun y => ENNReal.ofReal (min (y i : ℝ) M) with hg
  have hst := pi_stationary jump 0 hrec g
  have hG : ∑' z, pi jump 0 z * g z ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑' z, pi jump 0 z * (M : ℝ≥0∞)) ?_ ?_
    · rw [ENNReal.tsum_mul_right, pi_sum jump 0 hrec hfin, one_mul]; exact ENNReal.natCast_ne_top M
    · refine ENNReal.tsum_le_tsum fun z => mul_le_mul_right ?_ _
      simp only [hg]
      calc ENNReal.ofReal (min (z i : ℝ) M) ≤ ENNReal.ofReal M :=
            ENNReal.ofReal_le_ofReal (min_le_right _ _)
        _ = M := ENNReal.ofReal_natCast M
  have h1 : ∀ z, pi jump 0 z * ((∑' y, jump z y * g y) + ENNReal.ofReal (cc dat S i)) =
      pi jump 0 z * (Psi dat P (cc dat S i) i M z + g z) := by
    intro z; rw [claim1 dat P S jump hE hf hadm hjump i M z]
  have h2 := congrArg (fun F => ∑' z, F z) (funext h1)
  simp only [mul_add] at h2
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hst,
    pi_sum jump 0 hrec hfin, one_mul] at h2
  have h3 : (∑' z, pi jump 0 z * Psi dat P (cc dat S i) i M z) + ∑' z, pi jump 0 z * g z =
      ENNReal.ofReal (cc dat S i) + ∑' z, pi jump 0 z * g z := by rw [← h2, add_comm]
  exact (ENNReal.add_left_inj hG).1 h3

/-- Claim 3a: a pointwise upper bound. -/
lemma claim3a (i : Fin I) (M : ℕ) (z : Fin I → ℕ) :
    Psi dat P (cc dat S i) i M z ≤
      psi dat P (cc dat S i) i z + (if (M : ℝ) < z i then ENNReal.ofReal (cc dat S i) else 0) := by
  unfold Psi psi rhoE
  rw [add_assoc, ← int_add_const, ← int_const_add]
  refine lintegral_mono_ae ?_
  refine (ae_restrict_mem measurableSet_Ioo).mono fun u hu => ?_
  have hs := (hadm z u hu.1 hu.2).2
  obtain ⟨hr1, hr2⟩ := rr_bounds dat P S hadm i z hu
  have hc := cc_nonneg dat S i
  set d : ℝ := if (M : ℝ) < z i then cc dat S i else 0 with hd
  have hdof : (if (M : ℝ) < z i then ENNReal.ofReal (cc dat S i) else 0) = ENNReal.ofReal d := by
    rw [hd]; split_ifs <;> simp
  rw [hdof, ← add_assoc, ← tsum_pe_shift P hE (cc dat S i) i (rr dat P i z u) hr2,
    ← tsum_pe_add_const P hE]
  refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right ?_ _
  calc ENNReal.ofReal (Q (cc dat S i) M (nxt dat z e (P.f z u) i) (z i))
      ≤ ENNReal.ofReal (((e i : ℝ) - rr dat P i z u + cc dat S i) + d) :=
        ENNReal.ofReal_le_ofReal (Q_le hr2 (Nat.cast_nonneg _) (nxt_real dat z e _ hs i) hc)
    _ ≤ _ := ENNReal.ofReal_add_le

omit hE hf hadm in
lemma Psi_mono (i : Fin I) {M M' : ℕ} (z : Fin I → ℕ) (hzM : z i ≤ M) (hMM : M ≤ M') :
    Psi dat P (cc dat S i) i M z ≤ Psi dat P (cc dat S i) i M' z := by
  unfold Psi
  refine lintegral_mono fun u => ENNReal.tsum_le_tsum fun e => mul_le_mul_right ?_ _
  exact ENNReal.ofReal_le_ofReal (Q_mono (by exact_mod_cast hzM) hMM)

/-- Claim 3b: monotone limit. -/
lemma claim3b (i : Fin I) (z : Fin I → ℕ) :
    ⨆ M : ℕ, Psi dat P (cc dat S i) i (M + z i) z = psi dat P (cc dat S i) i z := by
  unfold Psi
  have hc := cc_nonneg dat S i
  rw [← lintegral_iSup]
  · unfold psi rhoE
    rw [← int_const_add]
    refine setLIntegral_congr_fun measurableSet_Ioo (fun u hu => ?_)
    have hs := (hadm z u hu.1 hu.2).2
    obtain ⟨hr1, hr2⟩ := rr_bounds dat P S hadm i z hu
    rw [← tsum_pe_shift P hE (cc dat S i) i (rr dat P i z u) hr2]
    simp_rw [← lintegral_count]
    rw [← lintegral_iSup]
    · congr 1; funext e
      rw [← ENNReal.mul_iSup]
      congr 1
      have : ∀ M : ℕ, Q (cc dat S i) (M + z i) (nxt dat z e (P.f z u) i) (z i) =
          min ((e i : ℝ) - rr dat P i z u) M + cc dat S i := by
        intro M
        rw [Q_shift (by push_cast; linarith) (nxt_real dat z e _ hs i)]
        congr 2; push_cast; ring
      simp_rw [this]
      exact iSup_ofReal_min _ _
    · intro M; exact measurable_of_countable _
    · intro M M' hMM e
      exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (Q_mono (by push_cast; linarith)
        (by omega))) _
  · intro M
    exact meas_comp P hf z (fun s => ∑' e, pe P e * ENNReal.ofReal (Q (cc dat S i) (M + z i) (nxt dat z e s i) (z i)))
  · intro M M' hMM u
    exact ENNReal.tsum_le_tsum fun e => mul_le_mul_right (ENNReal.ofReal_le_ofReal
      (Q_mono (by push_cast; linarith) (by omega))) _

/-- Claim 4. -/
lemma claim4 (hjump : IsPolicyChain dat P jump) (hrec : Stability.Recurrent jump 0)
    (hfin : Mtot jump 0 ≠ ⊤) (i : Fin I) :
    ∑' z, pi jump 0 z * psi dat P (cc dat S i) i z ≤ ENNReal.ofReal (cc dat S i) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  simp_rw [← claim3b dat P S hE hf hadm i, ENNReal.mul_iSup]
  rw [ENNReal.finsetSum_iSup_of_monotone]
  · refine iSup_le fun M => ?_
    set N := F.sup (fun z => z i) with hN
    calc ∑ z ∈ F, pi jump 0 z * Psi dat P (cc dat S i) i (M + z i) z
        ≤ ∑ z ∈ F, pi jump 0 z * Psi dat P (cc dat S i) i (M + N) z := by
          refine Finset.sum_le_sum fun z hz => mul_le_mul_right ?_ _
          have : z i ≤ N := Finset.le_sup (f := fun z => z i) hz
          exact Psi_mono dat P S i z (by omega) (by omega)
      _ ≤ ∑' z, pi jump 0 z * Psi dat P (cc dat S i) i (M + N) z := ENNReal.sum_le_tsum _
      _ = _ := claim2 dat P S jump hE hf hadm hjump hrec hfin i (M + N)
  · intro z M M' hMM
    exact mul_le_mul_right (Psi_mono dat P S i z (by omega) (by omega)) _

omit hE hf hadm in
lemma tail_tendsto (hrec : Stability.Recurrent jump 0) (hfin : Mtot jump 0 ≠ ⊤) (i : Fin I) :
    Filter.Tendsto (fun M : ℕ => ∑' z, pi jump 0 z * (if (M : ℝ) < z i then 1 else 0))
      Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  have h := ENNReal.tendsto_tsum_compl_atTop_zero (f := pi jump 0)
    (by rw [pi_sum jump 0 hrec hfin]; exact ENNReal.one_ne_top)
  obtain ⟨s, hs⟩ := ENNReal.tendsto_atTop_zero.1 h ε hε
  refine ⟨s.sup (fun z => z i), fun M hM => ?_⟩
  have h1 : ∑' z, pi jump 0 z * (if (M : ℝ) < z i then 1 else 0) =
      ∑' z : {z : Fin I → ℕ | (M : ℝ) < z i}, pi jump 0 z := by
    rw [tsum_subtype]
    congr 1; funext z
    simp only [Set.indicator, Set.mem_setOf_eq]
    split_ifs <;> simp
  rw [h1]
  refine le_trans ?_ (hs s le_rfl)
  refine ENNReal.tsum_mono_subtype _ fun z hz => ?_
  intro hzs
  have : z i ≤ s.sup (fun z => z i) := Finset.le_sup (f := fun z => z i) hzs
  have h2 : (M : ℝ) < z i := hz
  have h3 : z i ≤ M := le_trans this hM
  have h4 : (z i : ℝ) ≤ M := by exact_mod_cast h3
  linarith

/-- Claim 5. -/
lemma claim5 (hjump : IsPolicyChain dat P jump) (hrec : Stability.Recurrent jump 0)
    (hfin : Mtot jump 0 ≠ ⊤) (i : Fin I) :
    ENNReal.ofReal (cc dat S i) ≤ ∑' z, pi jump 0 z * psi dat P (cc dat S i) i z := by
  have ht := tail_tendsto jump hrec hfin i
  have ht2 := ENNReal.Tendsto.const_mul ht (a := ENNReal.ofReal (cc dat S i))
    (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at ht2
  have ht3 := ht2.const_add (∑' z, pi jump 0 z * psi dat P (cc dat S i) i z)
  rw [add_zero] at ht3
  refine ge_of_tendsto' ht3 fun M => ?_
  calc ENNReal.ofReal (cc dat S i) = ∑' z, pi jump 0 z * Psi dat P (cc dat S i) i M z :=
        (claim2 dat P S jump hE hf hadm hjump hrec hfin i M).symm
    _ ≤ ∑' z, pi jump 0 z * (psi dat P (cc dat S i) i z +
          (if (M : ℝ) < z i then ENNReal.ofReal (cc dat S i) else 0)) :=
        ENNReal.tsum_le_tsum fun z => mul_le_mul_right (claim3a dat P S hE hf hadm i M z) _
    _ = _ := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add]
        congr 1
        rw [← ENNReal.tsum_mul_left]
        congr 1; funext z
        split_ifs <;> simp [mul_comm, mul_left_comm]

/-- Claim 6: the balance identity in `ℝ≥0∞`. -/
lemma claim6 (hjump : IsPolicyChain dat P jump) (hrec : Stability.Recurrent jump 0)
    (hfin : Mtot jump 0 ≠ ⊤) (i : Fin I) :
    Lam P i + ∑' z, pi jump 0 z * rhoE dat P (cc dat S i) i z = ENNReal.ofReal (cc dat S i) := by
  have h := le_antisymm (claim4 dat P S jump hE hf hadm hjump hrec hfin i)
    (claim5 dat P S jump hE hf hadm hjump hrec hfin i)
  unfold psi at h
  simp_rw [mul_add] at h
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, pi_sum jump 0 hrec hfin, one_mul] at h
  exact h

end Analysis

/-! ### Part D: real conversions and the final assembly. -/

section Final
variable {I J : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  (dat : PacketNetworkData I J) (P : PacketPrimitives I J Ω)
  (S : Finset (Fin J → ℕ)) (jump : (Fin I → ℕ) → PMF (Fin I → ℕ))

noncomputable def vol (z : Fin I → ℕ) (s : Fin J → ℕ) : ℝ≥0∞ :=
  (volume.restrict (Set.Ioo (0:ℝ) 1)) {u | P.f z u = s}

noncomputable def w (z : Fin I → ℕ) (s : Fin J → ℕ) : ℝ := (vol P z s).toReal

noncomputable def rho (i : Fin I) (z : Fin I → ℕ) : ℝ :=
  ∑ s ∈ S, w P z s * (R dat).mulVec (realize s) i

noncomputable def W (s : Fin J → ℕ) : ℝ := ∑' z, (pi jump 0 z).toReal * w P z s

noncomputable def shat : Fin J → ℝ := ∑ s ∈ S, W P jump s • realize s

lemma vol_le_one (z : Fin I → ℕ) (s : Fin J → ℕ) : vol P z s ≤ 1 := by
  unfold vol
  refine le_trans (measure_mono (Set.subset_univ _)) ?_
  rw [Measure.restrict_apply_univ, vol_Ioo01]

lemma vol_ne_top (z : Fin I → ℕ) (s : Fin J → ℕ) : vol P z s ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (vol_le_one P z s)

lemma w_nonneg (z : Fin I → ℕ) (s : Fin J → ℕ) : 0 ≤ w P z s := ENNReal.toReal_nonneg

lemma w_le_one (z : Fin I → ℕ) (s : Fin J → ℕ) : w P z s ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact vol_le_one P z s)

variable (hf : ∀ z, Measurable (P.f z)) (hadm : IsAdmissibleMarkovianPolicy dat S P.f)
include hf hadm

lemma int_fin (z : Fin I → ℕ) (G : (Fin J → ℕ) → ℝ≥0∞) :
    ∫⁻ u in Set.Ioo (0:ℝ) 1, G (P.f z u) = ∑ s ∈ S, vol P z s * G s := by
  have h1 : ∀ u ∈ Set.Ioo (0:ℝ) 1,
      G (P.f z u) = ∑ s ∈ S, ({u | P.f z u = s}.indicator (fun _ => G s)) u := by
    intro u hu
    rw [Finset.sum_eq_single (P.f z u)]
    · simp [Set.indicator]
    · intro s _ hne
      simp [Set.indicator, Ne.symm hne]
    · intro h; exact absurd (hadm z u hu.1 hu.2).1 h
  rw [setLIntegral_congr_fun measurableSet_Ioo h1, lintegral_finset_sum]
  · refine Finset.sum_congr rfl fun s _ => ?_
    have hm : MeasurableSet {u : ℝ | P.f z u = s} := measurableSet_f_pre P hf z {s}
    rw [lintegral_indicator_const hm, mul_comm]
    rfl
  · intro s _; exact measurable_const.indicator (measurableSet_f_pre P hf z {s})

lemma vol_sum (z : Fin I → ℕ) : ∑ s ∈ S, vol P z s = 1 := by
  have h := int_fin dat P S hf hadm z (fun _ => 1)
  simp only [mul_one, lintegral_const, Measure.restrict_apply_univ, vol_Ioo01, one_mul] at h
  exact h.symm

lemma w_sum (z : Fin I → ℕ) : ∑ s ∈ S, w P z s = 1 := by
  unfold w
  rw [← ENNReal.toReal_sum (fun s _ => vol_ne_top P z s), vol_sum dat P S hf hadm z, ENNReal.toReal_one]

lemma rho_le (i : Fin I) (z : Fin I → ℕ) : rho dat P S i z ≤ cc dat S i := by
  unfold rho
  calc ∑ s ∈ S, w P z s * (R dat).mulVec (realize s) i ≤ ∑ s ∈ S, w P z s * cc dat S i :=
        Finset.sum_le_sum fun s hs => mul_le_mul_of_nonneg_left (abs_le.1 (abs_le_cc dat S i hs)).2
          (w_nonneg P z s)
    _ = cc dat S i := by rw [← Finset.sum_mul, w_sum dat P S hf hadm z, one_mul]

lemma neg_le_rho (i : Fin I) (z : Fin I → ℕ) : -cc dat S i ≤ rho dat P S i z := by
  unfold rho
  calc -cc dat S i = ∑ s ∈ S, w P z s * (-cc dat S i) := by
        rw [← Finset.sum_mul, w_sum dat P S hf hadm z, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun s hs => mul_le_mul_of_nonneg_left (abs_le.1 (abs_le_cc dat S i hs)).1
          (w_nonneg P z s)

lemma abs_rho_le (i : Fin I) (z : Fin I → ℕ) : |rho dat P S i z| ≤ cc dat S i :=
  abs_le.2 ⟨neg_le_rho dat P S hf hadm i z, rho_le dat P S hf hadm i z⟩

lemma rhoE_eq (i : Fin I) (z : Fin I → ℕ) :
    rhoE dat P (cc dat S i) i z = ENNReal.ofReal (cc dat S i - rho dat P S i z) := by
  unfold rhoE
  calc ∫⁻ u in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (cc dat S i - rr dat P i z u)
      = ∑ s ∈ S, vol P z s * ENNReal.ofReal (cc dat S i - (R dat).mulVec (realize s) i) :=
        int_fin dat P S hf hadm z (fun s => ENNReal.ofReal (cc dat S i - (R dat).mulVec (realize s) i))
    _ = ∑ s ∈ S, ENNReal.ofReal (w P z s * (cc dat S i - (R dat).mulVec (realize s) i)) :=
        Finset.sum_congr rfl fun s _ => by
          rw [ENNReal.ofReal_mul (w_nonneg P z s), w, ENNReal.ofReal_toReal (vol_ne_top P z s)]
    _ = ENNReal.ofReal (∑ s ∈ S, w P z s * (cc dat S i - (R dat).mulVec (realize s) i)) :=
        (ENNReal.ofReal_sum_of_nonneg fun s hs => mul_nonneg (w_nonneg P z s)
          (sub_nonneg.2 (abs_le.1 (abs_le_cc dat S i hs)).2)).symm
    _ = _ := by
        congr 1
        simp only [rho, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, w_sum dat P S hf hadm z, one_mul]

variable (hE : AEMeasurable (P.Eincr 1) ℙ)
include hE

lemma Lam_ne_top (hjump : IsPolicyChain dat P jump) (hrec : Stability.Recurrent jump 0)
    (hfin : Mtot jump 0 ≠ ⊤) (i : Fin I) : Lam P i ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal (cc dat S i)) ENNReal.ofReal_ne_top ?_
  rw [← claim6 dat P S jump hE hf hadm hjump hrec hfin i]
  exact le_self_add

omit hf hadm hE in
lemma pi_summable (hrec : Stability.Recurrent jump 0) (hfin : Mtot jump 0 ≠ ⊤) :
    Summable (fun z => (pi jump 0 z).toReal) :=
  ENNReal.summable_toReal (by rw [pi_sum jump 0 hrec hfin]; exact ENNReal.one_ne_top)

omit hf hadm hE in
lemma pi_toReal_sum (hrec : Stability.Recurrent jump 0) (hfin : Mtot jump 0 ≠ ⊤) :
    ∑' z, (pi jump 0 z).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (pi_ne_top jump 0 hrec hfin), pi_sum jump 0 hrec hfin, ENNReal.toReal_one]

omit hE in
lemma rho_summable (hrec : Stability.Recurrent jump 0) (hfin : Mtot jump 0 ≠ ⊤) (i : Fin I) :
    Summable (fun z => (pi jump 0 z).toReal * rho dat P S i z) := by
  refine Summable.of_norm_bounded ((pi_summable jump hrec hfin).mul_right (cc dat S i)) fun z => ?_
  rw [norm_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (abs_rho_le dat P S hf hadm i z) ENNReal.toReal_nonneg

/-- the balance identity in real form -/
lemma balance_real (hjump : IsPolicyChain dat P jump) (hrec : Stability.Recurrent jump 0)
    (hfin : Mtot jump 0 ≠ ⊤) (i : Fin I) :
    (Lam P i).toReal = ∑' z, (pi jump 0 z).toReal * rho dat P S i z := by
  have h := claim6 dat P S jump hE hf hadm hjump hrec hfin i
  simp_rw [rhoE_eq dat P S hf hadm i] at h
  have hc := cc_nonneg dat S i
  have hsum : ∑' z, pi jump 0 z * ENNReal.ofReal (cc dat S i - rho dat P S i z) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑' z, pi jump 0 z * ENNReal.ofReal (2 * cc dat S i)) ?_ ?_
    · rw [ENNReal.tsum_mul_right, pi_sum jump 0 hrec hfin, one_mul]; exact ENNReal.ofReal_ne_top
    · exact ENNReal.tsum_le_tsum fun z => mul_le_mul_right (ENNReal.ofReal_le_ofReal
        (by linarith [neg_le_rho dat P S hf hadm i z])) _
  have h2 := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add (Lam_ne_top dat P S jump hf hadm hE hjump hrec hfin i) hsum,
    ENNReal.tsum_toReal_eq (fun z => ENNReal.mul_ne_top (pi_ne_top jump 0 hrec hfin z) ENNReal.ofReal_ne_top),
    ENNReal.toReal_ofReal hc] at h2
  simp_rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.2 (rho_le dat P S hf hadm i _)),
    mul_sub] at h2
  rw [Summable.tsum_sub ((pi_summable jump hrec hfin).mul_right _) (rho_summable dat P S jump hf hadm hrec hfin i),
    tsum_mul_right, pi_toReal_sum jump hrec hfin, one_mul] at h2
  linarith

omit hf hadm in
lemma lam_eq (lam : Fin I → ℝ) (hP : PrimitiveAssumptions P lam) (i : Fin I) :
    lam i = (Lam P i).toReal := by
  rw [← hP.arrival_mean i]
  have hmeas : AEStronglyMeasurable (fun ω => (P.Eincr 1 ω i : ℝ)) ℙ :=
    ((measurable_of_countable (fun e : Fin I → ℕ => (e i : ℝ))).comp_aemeasurable hE).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun ω => Nat.cast_nonneg _)) hmeas]
  congr 1
  simp_rw [ENNReal.ofReal_natCast]
  exact (tsum_prob_mul P hE (fun e => (e i : ℝ≥0∞))).symm

omit hE in
lemma f0 {u : ℝ} (hu : u ∈ Set.Ioo (0:ℝ) 1) : P.f 0 u = 0 := by
  funext j
  have h := (hadm 0 u hu.1 hu.2).2 (dat.u j)
  simp only [Matrix.mulVec, dotProduct, B, Pi.zero_apply, Nat.cast_zero] at h
  have h2 : ((P.f 0 u j : ℕ) : ℝ) ≤
      ∑ j', (if dat.u j' = dat.u j then (1:ℝ) else 0) * (P.f 0 u j' : ℝ) := by
    have := Finset.single_le_sum
      (f := fun j' => (if dat.u j' = dat.u j then (1:ℝ) else 0) * (P.f 0 u j' : ℝ))
      (fun j' _ => by split_ifs <;> simp) (Finset.mem_univ j)
    simpa using this
  have h3 : ((P.f 0 u j : ℕ) : ℝ) ≤ 0 := le_trans h2 h
  have h4 : P.f 0 u j ≤ 0 := by exact_mod_cast h3
  simpa using h4

omit hE in
lemma zero_mem_S : (0 : Fin J → ℕ) ∈ S := by
  have := (hadm 0 (1/2) (by norm_num) (by norm_num)).1
  rwa [f0 dat P S hf hadm (by norm_num)] at this

omit hE in
lemma w00 : w P 0 0 = 1 := by
  unfold w vol
  have hm : MeasurableSet {u : ℝ | P.f 0 u = 0} := measurableSet_f_pre P hf 0 {0}
  rw [Measure.restrict_apply hm]
  have hI : {u : ℝ | P.f 0 u = 0} ∩ Set.Ioo (0:ℝ) 1 = Set.Ioo (0:ℝ) 1 :=
    Set.inter_eq_right.2 (fun u hu => f0 dat P S hf hadm hu)
  rw [hI, vol_Ioo01, ENNReal.toReal_one]

omit hf hadm hE in
lemma W_summable (hrec : Stability.Recurrent jump 0) (hfin : Mtot jump 0 ≠ ⊤) (s : Fin J → ℕ) :
    Summable (fun z => (pi jump 0 z).toReal * w P z s) := by
  refine Summable.of_norm_bounded (pi_summable jump hrec hfin) fun z => ?_
  rw [norm_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg, Real.norm_of_nonneg (w_nonneg P z s)]
  exact mul_le_of_le_one_right ENNReal.toReal_nonneg (w_le_one P z s)

omit hf hadm hE in
lemma W_nonneg (s : Fin J → ℕ) : 0 ≤ W P jump s :=
  tsum_nonneg fun z => mul_nonneg ENNReal.toReal_nonneg (w_nonneg P z s)

omit hE in
lemma W_sum (hrec : Stability.Recurrent jump 0) (hfin : Mtot jump 0 ≠ ⊤) :
    ∑ s ∈ S, W P jump s = 1 := by
  unfold W
  rw [← Summable.tsum_finsetSum (fun s _ => W_summable P jump hrec hfin s)]
  simp_rw [← Finset.mul_sum, w_sum dat P S hf hadm, mul_one]
  exact pi_toReal_sum jump hrec hfin

omit hE in
lemma W0_pos (hrec : Stability.Recurrent jump 0) (hfin : Mtot jump 0 ≠ ⊤) : 0 < W P jump 0 := by
  have h1 : 0 < (pi jump 0 0).toReal * w P 0 0 := by
    rw [w00 dat P S hf hadm, mul_one]
    exact ENNReal.toReal_pos (pi_x0_pos jump 0 hrec hfin).ne' (pi_ne_top jump 0 hrec hfin 0)
  refine lt_of_lt_of_le h1 ((W_summable P jump hrec hfin 0).le_tsum 0 fun z _ => ?_)
  exact mul_nonneg ENNReal.toReal_nonneg (w_nonneg P z 0)

omit hE in
lemma shat_mem (hrec : Stability.Recurrent jump 0) (hfin : Mtot jump 0 ≠ ⊤) :
    shat P S jump ∈ hullFinset S := by
  unfold shat hullFinset
  exact (convex_convexHull ℝ _).sum_mem (fun s _ => W_nonneg P jump s) (W_sum dat P S jump hf hadm hrec hfin)
    (fun s hs => subset_convexHull ℝ _ (Set.mem_image_of_mem _ hs))

omit hf hadm hE in
lemma mulVec_shat {n : ℕ} (A : Matrix (Fin n) (Fin J) ℝ) (k : Fin n) :
    A.mulVec (shat P S jump) k = ∑ s ∈ S, W P jump s * A.mulVec (realize s) k := by
  simp only [shat, Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

lemma R_shat (lam : Fin I → ℝ) (hP : PrimitiveAssumptions P lam) (hjump : IsPolicyChain dat P jump)
    (hrec : Stability.Recurrent jump 0) (hfin : Mtot jump 0 ≠ ⊤) :
    (R dat).mulVec (shat P S jump) = lam := by
  funext i
  rw [mulVec_shat, lam_eq P hE lam hP i, balance_real dat P S jump hf hadm hE hjump hrec hfin i]
  simp only [W]
  simp_rw [← tsum_mul_right]
  rw [← Summable.tsum_finsetSum (fun s _ => (W_summable P jump hrec hfin s).mul_right _)]
  congr 1; funext z
  simp only [rho, Finset.mul_sum, mul_assoc]

omit hf hadm hE in
lemma exists_cbar {K : ℕ} (cfg : LinkConfigData J K) (h124 : SatisfiesAssumption124 cfg)
    (hC : cfg.C.Nonempty) : ∃ cbar ∈ hullFinset cfg.C, ∀ k, 0 < cbar k := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    obtain ⟨c0, hc0⟩ := hC
    exact ⟨realize c0, subset_convexHull ℝ _ (Set.mem_image_of_mem _ hc0), fun k => k.elim0⟩
  · choose ck hck using h124
    refine ⟨∑ k, (1 / (K:ℝ)) • realize (ck k), ?_, ?_⟩
    · refine (convex_convexHull ℝ _).sum_mem (fun _ _ => by positivity) ?_
        (fun k _ => subset_convexHull ℝ _ (Set.mem_image_of_mem _ (hck k).1))
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · intro k
      rw [Finset.sum_apply]
      refine lt_of_lt_of_le ?_ (Finset.single_le_sum
        (f := fun k' => ((1 / (K:ℝ)) • realize (ck k')) k)
        (fun k' _ => by simp only [Pi.smul_apply, smul_eq_mul, realize]; positivity) (Finset.mem_univ k))
      simp only [Pi.smul_apply, smul_eq_mul, realize]
      have : (0:ℝ) < ck k k := by exact_mod_cast (hck k).2
      positivity

omit hf hadm hE in
lemma realize_zero : realize (0 : Fin J → ℕ) = 0 := by
  funext j; simp [realize]

end Final

/-- The main theorem: stability implies subcriticality. -/
theorem sis_core {I J K : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (dat : PacketNetworkData I J) (_h121 : SatisfiesAssumption121 dat)
    (cfg : LinkConfigData J K) (h124 : SatisfiesAssumption124 cfg)
    (S : Finset (Fin J → ℕ)) (hS : IsScheduleSet cfg S)
    (lam : Fin I → ℝ) (P : PacketPrimitives I J Ω) (hP : PrimitiveAssumptions P lam)
    (jump : (Fin I → ℕ) → PMF (Fin I → ℕ))
    (hstable : IsStableMarkovianPolicy dat S P jump) :
    lam ∈ subcriticalRegion dat S cfg := by
  obtain ⟨hadm, hjump, _hirr, hpr⟩ := hstable
  have hrec : Stability.Recurrent jump 0 := (hpr 0).1
  have hfin : Mtot jump 0 ≠ ⊤ := by rw [Mtot_eq]; exact (hpr 0).2.ne
  have hf : ∀ z, Measurable (P.f z) := hP.policy_measurable
  have hE : AEMeasurable (P.Eincr 1) ℙ := (hP.arrivals_ident 0).aemeasurable_snd
  have hR := R_shat dat P S jump hf hadm hE lam hP hjump hrec hfin
  have h0S := zero_mem_S dat P S hf hadm
  have hC : cfg.C.Nonempty := by
    obtain ⟨c, hc, _⟩ := (hS 0).1 h0S
    exact ⟨c, hc⟩
  obtain ⟨cbar, hcbar, hcpos⟩ := exists_cbar cfg h124 hC
  choose cs hcs using fun s (hs : s ∈ S) => (hS s).1 hs
  let cvec : (Fin J → ℕ) → (Fin K → ℝ) := fun s =>
    if h : s ∈ S then (if s = 0 then cbar else realize (cs s h)) else 0
  have hW0 := W0_pos dat P S jump hf hadm hrec hfin
  refine ⟨?_, shat P S jump, shat_mem dat P S jump hf hadm hrec hfin,
    ∑ s ∈ S, W P jump s • cvec s, ?_, hR, ?_⟩
  · intro i
    rw [lam_eq P hE lam hP i]
    exact ENNReal.toReal_nonneg
  · unfold hullFinset
    refine (convex_convexHull ℝ _).sum_mem (fun s _ => W_nonneg P jump s)
      (W_sum dat P S jump hf hadm hrec hfin) (fun s hs => ?_)
    simp only [cvec, dif_pos hs]
    split_ifs
    · exact hcbar
    · exact subset_convexHull ℝ _ (Set.mem_image_of_mem _ (hcs s hs).1)
  · intro k
    rw [mulVec_shat, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_lt_sum (fun s hs => ?_) ⟨0, h0S, ?_⟩
    · refine mul_le_mul_of_nonneg_left ?_ (W_nonneg P jump s)
      simp only [cvec, dif_pos hs]
      split_ifs with h0
      · subst h0
        rw [realize_zero, Matrix.mulVec_zero]
        exact (hcpos k).le
      · exact (hcs s hs).2 k
    · simp only [cvec, dif_pos h0S, if_pos rfl]
      rw [realize_zero, Matrix.mulVec_zero]
      simp only [Pi.zero_apply, mul_zero]
      exact mul_pos hW0 (hcpos k)

end SIS

end ProcessingNetworks.PacketNetworks

open ProcessingNetworks.PacketNetworks
open MeasureTheory ProbabilityTheory

theorem solution
    {I J K : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (dat : PacketNetworkData I J) (h121 : SatisfiesAssumption121 dat)
    (cfg : LinkConfigData J K) (h124 : SatisfiesAssumption124 cfg)
    (S : Finset (Fin J → ℕ)) (hS : IsScheduleSet cfg S)
    (lam : Fin I → ℝ) (P : PacketPrimitives I J Ω) (hP : PrimitiveAssumptions P lam)
    (jump : (Fin I → ℕ) → PMF (Fin I → ℕ))
    (hstable : IsStableMarkovianPolicy dat S P jump) :
    lam ∈ subcriticalRegion dat S cfg := by
  exact SIS.sis_core dat h121 cfg h124 S hS lam P hP jump hstable
