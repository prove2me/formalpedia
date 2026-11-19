-- Prove2me | solution 1 for PrivLearn.LocalSim.theorem_5_7
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T01:38:23.704911+00:00
-- url     : https://prove2.me/submissions/47faee15-079f-46ad-b34e-c54cd797e3bf

import Mathlib
import Definitions.Def_PrivLearn_LocalSim_Privacy
import Definitions.Def_PrivLearn_LocalSim_Simulation
import Theorems.Thm_PrivLearn_LocalSim_randomizer_is_local
import Theorems.Thm_PrivLearn_LocalSim_lemma_5_6

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LSAux

open MeasureTheory Set

/-- `Lap(s)` is a probability measure for `s > 0`. -/
lemma laplace_univ (s : ℝ) (hs : 0 < s) : PrivLearn.Generic.laplace s univ = 1 := by
  have hm1 : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-|x| / s) / (2 * s))) := by
    fun_prop
  unfold PrivLearn.Generic.laplace
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h_prod : (fun x : ℝ => ENNReal.ofReal (Real.exp (-|x| / s) / (2 * s))) =
      fun x : ℝ => ENNReal.ofReal (1 / (2 * s)) * ENNReal.ofReal (Real.exp (-|x| / s)) := by
    ext x
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [h_prod, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_add_compl _ measurableSet_Iic, compl_Iic]
  have ha₁ : (0 : ℝ) < 1 / s := by positivity
  have ha₂ : -(1 / s) < 0 := by linarith
  have h_iic : (∫⁻ x in Iic (0 : ℝ), ENNReal.ofReal (Real.exp (-|x| / s))) =
      ENNReal.ofReal (1 / (1 / s)) := by
    have heq : EqOn (fun x : ℝ => ENNReal.ofReal (Real.exp (-|x| / s)))
        (fun x : ℝ => ENNReal.ofReal (Real.exp ((1 / s) * x))) (Iic 0) := by
      intro x hx
      simp only
      rw [abs_of_nonpos hx]
      ring_nf
    rw [setLIntegral_congr_fun measurableSet_Iic heq,
      ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Iic ha₁ 0)
        (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le),
      integral_exp_mul_Iic ha₁ 0]
    simp
  have h_ioi : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-|x| / s))) =
      ENNReal.ofReal (-1 / (-(1 / s))) := by
    have heq : EqOn (fun x : ℝ => ENNReal.ofReal (Real.exp (-|x| / s)))
        (fun x : ℝ => ENNReal.ofReal (Real.exp ((-(1 / s)) * x))) (Ioi 0) := by
      intro x hx
      simp only
      rw [abs_of_pos hx]
      ring_nf
    rw [setLIntegral_congr_fun measurableSet_Ioi heq,
      ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Ioi ha₂ 0)
        (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le),
      integral_exp_mul_Ioi ha₂ 0]
    simp [neg_div]
  rw [h_iic, h_ioi, ← ENNReal.ofReal_add (by positivity) (by
      rw [neg_div_neg_eq]; positivity), ← ENNReal.ofReal_mul (by positivity)]
  rw [← ENNReal.ofReal_one]
  congr 1
  field_simp
  ring

instance laplace_isProb (s : ℝ) [Fact (0 < s)] :
    IsProbabilityMeasure (PrivLearn.Generic.laplace s) :=
  ⟨laplace_univ s Fact.out⟩

lemma laplace_isProb' (s : ℝ) (hs : 0 < s) : IsProbabilityMeasure (PrivLearn.Generic.laplace s) :=
  ⟨laplace_univ s hs⟩

lemma laplace_sigmaFinite (s : ℝ) : SigmaFinite (PrivLearn.Generic.laplace s) := by
  unfold PrivLearn.Generic.laplace
  infer_instance

/-- Shifting by `δ` with `|δ| ≤ 2b` changes `Lap(2b/ε)`-probabilities by at most `e^ε`
(from `randomizer_is_local`). -/
lemma laplace_shift (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε) (δ : ℝ) (hδ : |δ| ≤ 2 * b) (X : Set ℝ)
    (hX : MeasurableSet X) :
    PrivLearn.Generic.laplace (2 * b / ε) {x | x + δ ∈ X} ≤
      ENNReal.ofReal (Real.exp ε) * PrivLearn.Generic.laplace (2 * b / ε) X := by
  set g : Bool → ℝ := fun u => if u then δ / 2 else -(δ / 2) with hg
  have hgb : ∀ u, |g u| ≤ b := by
    intro u
    cases u <;> simp [hg, abs_div] <;> linarith
  have hloc := PrivLearn.LocalSim.randomizer_is_local g b ε hb hε hgb true false
    {y | y + δ / 2 ∈ X} (measurable_add_const _ hX)
  unfold PrivLearn.LocalSim.randomizerLaw at hloc
  have hS : MeasurableSet {y : ℝ | y + δ / 2 ∈ X} := measurable_add_const _ hX
  rw [Measure.map_apply (measurable_const_add _) hS,
    Measure.map_apply (measurable_const_add _) hS] at hloc
  have e1 : (fun η => g true + η) ⁻¹' {y | y + δ / 2 ∈ X} = {x | x + δ ∈ X} := by
    ext x; simp only [hg, mem_preimage, mem_ofPred_eq, if_true]; ring_nf
  have e2 : (fun η => g false + η) ⁻¹' {y | y + δ / 2 ∈ X} = X := by
    ext x; simp only [hg, mem_preimage, mem_ofPred_eq]; simp
  rwa [e1, e2] at hloc

/-- A section bound for a product of identical measures over `Fin (n+1)`. -/
lemma pi_le_of_section {α : Type*} [MeasurableSpace α] (ν : Measure α) [SigmaFinite ν] {n : ℕ}
    (k : Fin (n + 1)) {E F : Set (Fin (n + 1) → α)} (hE : MeasurableSet E)
    (hF : MeasurableSet F) (c : ENNReal)
    (h : ∀ r : Fin n → α, ν {x | Fin.insertNth k x r ∈ E} ≤
      c * ν {x | Fin.insertNth k x r ∈ F}) :
    Measure.pi (fun _ => ν) E ≤ c * Measure.pi (fun _ => ν) F := by
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) k).symm
  rw [← hmp.measure_preimage hE.nullMeasurableSet, ← hmp.measure_preimage hF.nullMeasurableSet,
    Measure.prod_apply_symm (hmp.measurable hE), Measure.prod_apply_symm (hmp.measurable hF),
    ← lintegral_const_mul _ (measurable_measure_prodMk_right (hmp.measurable hF))]
  refine lintegral_mono fun r => ?_
  have e : ∀ S : Set (Fin (n + 1) → α), (fun x => (x, r)) ⁻¹'
      ((MeasurableEquiv.piFinSuccAbove (fun _ => α) k).symm ⁻¹' S) =
        {x | Fin.insertNth k x r ∈ S} := fun S => rfl
  rw [e, e]
  exact h r

end LSAux
namespace LSAux

open MeasureTheory PrivLearn.LocalSim

variable {Dom Out : Type} {t : ℕ}

/-- Block data: for each query, the `m` data entries of its block and the `m` noises. -/
abbrev Blk (Dom : Type) (m : ℕ) := (Fin m → Dom) × (Fin m → ℝ)

/-- The simulated answers as a function of the block data. -/
noncomputable def ans (A : SQAlg Dom Out t) (m : ℕ) (D : Fin t → Blk Dom m) :
    (k : ℕ) → k < t → ℝ
  | k, hk =>
    (1 / (m : ℝ)) * ∑ i : Fin m,
      (A.query ⟨k, hk⟩ (fun j : Fin k => ans A m D j.1 (lt_trans j.2 hk)) ((D ⟨k, hk⟩).1 i) +
        (D ⟨k, hk⟩).2 i)

/-- The answers before query `k`. -/
noncomputable def pre (A : SQAlg Dom Out t) (m : ℕ) (D : Fin t → Blk Dom m) (k : Fin t) :
    Fin k → ℝ :=
  fun j => ans A m D j.1 (lt_trans j.2 k.2)

lemma ans_eq (A : SQAlg Dom Out t) (m : ℕ) (D : Fin t → Blk Dom m) (k : ℕ) (hk : k < t) :
    ans A m D k hk = (1 / (m : ℝ)) * ∑ i : Fin m,
      (A.query ⟨k, hk⟩ (pre A m D ⟨k, hk⟩) ((D ⟨k, hk⟩).1 i) + (D ⟨k, hk⟩).2 i) := by
  rw [ans]
  rfl

lemma ans_congr (A : SQAlg Dom Out t) (m : ℕ) (D D' : Fin t → Blk Dom m) (k : ℕ) :
    ∀ (hk : k < t), (∀ j : Fin t, j.1 ≤ k → D j = D' j) → ans A m D k hk = ans A m D' k hk := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hD
    rw [ans_eq, ans_eq]
    have hpre : pre A m D ⟨k, hk⟩ = pre A m D' ⟨k, hk⟩ := by
      funext j
      exact ih j.1 j.2 _ fun j' hj' => hD j' (hj'.trans j.2.le)
    rw [hpre, hD ⟨k, hk⟩ le_rfl]

lemma pre_congr (A : SQAlg Dom Out t) (m : ℕ) (D D' : Fin t → Blk Dom m) (k : Fin t)
    (hD : ∀ j : Fin t, j.1 < k.1 → D j = D' j) : pre A m D k = pre A m D' k := by
  funext j
  exact ans_congr A m D D' j.1 _ fun j' hj' => hD j' (lt_of_le_of_lt hj' j.2)

lemma measurable_ans [MeasurableSpace Dom] (A : SQAlg Dom Out t) (m : ℕ)
    (hq : ∀ k : Fin t, Measurable fun p : (Fin k → ℝ) × Dom => A.query k p.1 p.2) (k : ℕ) :
    ∀ (hk : k < t), Measurable fun D : Fin t → Blk Dom m => ans A m D k hk := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hpre : Measurable fun D : Fin t → Blk Dom m => pre A m D ⟨k, hk⟩ :=
      measurable_pi_lambda _ fun j => ih j.1 j.2 _
    simp_rw [ans_eq]
    refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _
    refine Measurable.add ?_ ?_
    · exact (hq ⟨k, hk⟩).comp (hpre.prodMk ((measurable_pi_apply i).comp
        (measurable_fst.comp (measurable_pi_apply _))))
    · exact (measurable_pi_apply i).comp (measurable_snd.comp (measurable_pi_apply _))

lemma measurable_pre [MeasurableSpace Dom] (A : SQAlg Dom Out t) (m : ℕ)
    (hq : ∀ k : Fin t, Measurable fun p : (Fin k → ℝ) × Dom => A.query k p.1 p.2) (k : Fin t) :
    Measurable fun D : Fin t → Blk Dom m => pre A m D k :=
  measurable_pi_lambda _ fun j => measurable_ans A m hq j.1 _

/-- The block data of the simulation run on the database `z` with the noises `η`. -/
def blocks {m n : ℕ} (h : t * m ≤ n) (z : Fin n → Dom) (η : Fin t → Fin m → ℝ) :
    Fin t → Blk Dom m :=
  fun k => (fun i => z (blockIdx h k i), η k)

lemma simAnswer_eq (A : SQAlg Dom Out t) {m n : ℕ} (h : t * m ≤ n) (z : Fin n → Dom)
    (η : Fin t → Fin m → ℝ) (k : ℕ) :
    ∀ (hk : k < t), simAnswer A m h z η k hk = ans A m (blocks h z η) k hk := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [simAnswer, ans]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    funext j
    exact ih j.1 j.2 _

lemma simTranscript_eq (A : SQAlg Dom Out t) {m n : ℕ} (h : t * m ≤ n) (z : Fin n → Dom)
    (η : Fin t → Fin m → ℝ) :
    simTranscript A m h z η = fun k => ans A m (blocks h z η) k.1 k.2 := by
  funext k
  exact simAnswer_eq A h z η k.1 k.2

lemma measurable_blocks_noise [MeasurableSpace Dom] {m n : ℕ} (h : t * m ≤ n)
    (z : Fin n → Dom) : Measurable fun η : Fin t → Fin m → ℝ => blocks h z η :=
  measurable_pi_lambda _ fun k => measurable_const.prodMk (measurable_pi_apply k)

lemma blockIdx_inj {m n : ℕ} (h : t * m ≤ n) {k k' : Fin t} {i i' : Fin m}
    (he : blockIdx h k i = blockIdx h k' i') : k = k' ∧ i = i' := by
  unfold blockIdx at he
  have h1 := (Fin.castLE_injective h) he
  have h2 := finProdFinEquiv.injective h1
  exact Prod.ext_iff.1 h2

lemma insertNth_ne {α : Type*} {n : ℕ} (k : Fin (n + 1)) (y y' : α) (r : Fin n → α)
    (j : Fin (n + 1)) (hj : j ≠ k) :
    Fin.insertNth (α := fun _ => α) k y r j = Fin.insertNth (α := fun _ => α) k y' r j := by
  obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
  simp [Fin.insertNth_apply_succAbove]

lemma measurable_insertNth' {α : Type*} [MeasurableSpace α] {n : ℕ} (k : Fin (n + 1))
    (r : Fin n → α) : Measurable fun y : α => Fin.insertNth (α := fun _ => α) k y r :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => α) k).symm.measurable.comp
    (measurable_id.prodMk measurable_const)

end LSAux
namespace LSAux

open MeasureTheory PrivLearn.LocalSim

variable {Dom Out : Type}

/-- The noise array with value `x` at `(k₀, i₀)`, the rest of block `k₀` given by `q` and the
other blocks given by `r`. -/
def Yf {t' m' : ℕ} (k₀ : Fin (t' + 1)) (i₀ : Fin (m' + 1)) (r : Fin t' → Fin (m' + 1) → ℝ)
    (q : Fin m' → ℝ) (x : ℝ) : Fin (t' + 1) → Fin (m' + 1) → ℝ :=
  Fin.insertNth (α := fun _ => Fin (m' + 1) → ℝ) k₀ (Fin.insertNth (α := fun _ => ℝ) i₀ x q) r

lemma Yf_ne {t' m' : ℕ} (k₀ : Fin (t' + 1)) (i₀ : Fin (m' + 1)) (r : Fin t' → Fin (m' + 1) → ℝ)
    (q : Fin m' → ℝ) (x x' : ℝ) (j : Fin (t' + 1)) (hj : j ≠ k₀) :
    Yf k₀ i₀ r q x j = Yf k₀ i₀ r q x' j :=
  insertNth_ne k₀ _ _ r j hj

lemma Yf_same {t' m' : ℕ} (k₀ : Fin (t' + 1)) (i₀ : Fin (m' + 1))
    (r : Fin t' → Fin (m' + 1) → ℝ) (q : Fin m' → ℝ) (x : ℝ) :
    Yf k₀ i₀ r q x k₀ = Fin.insertNth (α := fun _ => ℝ) i₀ x q := by
  simp [Yf]

lemma measurable_Yf {t' m' : ℕ} (k₀ : Fin (t' + 1)) (i₀ : Fin (m' + 1))
    (r : Fin t' → Fin (m' + 1) → ℝ) (q : Fin m' → ℝ) : Measurable (Yf k₀ i₀ r q) :=
  (measurable_insertNth' k₀ r).comp (measurable_insertNth' i₀ q)

/-- The coupling behind privacy: the run on `z` with noise `Y x` equals the run on `z'` with
noise `Y (x + δ)`, where `δ = g(z_{i*}) − g(z'_{i*})` for the query `g` asked at block `k₀`. -/
lemma shift_coupling {t' m' n : ℕ} (A : SQAlg Dom Out (t' + 1)) (h : (t' + 1) * (m' + 1) ≤ n)
    (z z' : Fin n → Dom) (k₀ : Fin (t' + 1)) (i₀ : Fin (m' + 1))
    (hsame : ∀ j, j ≠ blockIdx h k₀ i₀ → z j = z' j)
    (r : Fin t' → Fin (m' + 1) → ℝ) (q : Fin m' → ℝ) (δ : ℝ)
    (hδ : δ = A.query k₀ (pre A (m' + 1) (blocks h z (Yf k₀ i₀ r q 0)) k₀) (z (blockIdx h k₀ i₀)) -
      A.query k₀ (pre A (m' + 1) (blocks h z (Yf k₀ i₀ r q 0)) k₀) (z' (blockIdx h k₀ i₀)))
    (x : ℝ) :
    simTranscript A (m' + 1) h z (Yf k₀ i₀ r q x) =
      simTranscript A (m' + 1) h z' (Yf k₀ i₀ r q (x + δ)) := by
  rw [simTranscript_eq, simTranscript_eq]
  funext K
  suffices H : ∀ k (hk : k < t' + 1), ans A (m' + 1) (blocks h z (Yf k₀ i₀ r q x)) k hk =
      ans A (m' + 1) (blocks h z' (Yf k₀ i₀ r q (x + δ))) k hk from H K.1 K.2
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [ans_eq, ans_eq]
    have hpre : pre A (m' + 1) (blocks h z (Yf k₀ i₀ r q x)) ⟨k, hk⟩ =
        pre A (m' + 1) (blocks h z' (Yf k₀ i₀ r q (x + δ))) ⟨k, hk⟩ := by
      funext j
      exact ih j.1 j.2 _
    rw [← hpre]
    by_cases hkk : (⟨k, hk⟩ : Fin (t' + 1)) = k₀
    · subst hkk
      have hp0 : pre A (m' + 1) (blocks h z (Yf ⟨k, hk⟩ i₀ r q x)) ⟨k, hk⟩ =
          pre A (m' + 1) (blocks h z (Yf ⟨k, hk⟩ i₀ r q 0)) ⟨k, hk⟩ := by
        apply pre_congr
        intro j hj
        have hjne : j ≠ ⟨k, hk⟩ := fun e => by rw [e] at hj; exact lt_irrefl _ hj
        simp only [blocks]
        rw [Yf_ne _ i₀ r q x 0 j hjne]
      rw [hp0]
      congr 1
      rw [Fin.sum_univ_succAbove _ i₀, Fin.sum_univ_succAbove _ i₀]
      simp only [blocks, Yf_same, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      congr 1
      · rw [hδ]
        ring
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [hsame _ fun he => Fin.succAbove_ne i₀ j (blockIdx_inj h he).2]
    · have hblk : blocks h z (Yf k₀ i₀ r q x) ⟨k, hk⟩ =
          blocks h z' (Yf k₀ i₀ r q (x + δ)) ⟨k, hk⟩ := by
        simp only [blocks]
        rw [Yf_ne k₀ i₀ r q x (x + δ) _ hkk]
        congr 1
        funext i
        exact hsame _ fun he => hkk (blockIdx_inj h he).1
      rw [hblk]

variable [MeasurableSpace Dom] [MeasurableSpace Out]

/-- Part 1 of Theorem 5.7: the simulation is ε-differentially private. -/
lemma privacy {t : ℕ} (A : SQAlg Dom Out t) (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε)
    (hqb : ∀ (k : Fin t) (a : Fin k → ℝ) (u : Dom), |A.query k a u| ≤ b)
    (hq : ∀ k : Fin t, Measurable fun p : (Fin k → ℝ) × Dom => A.query k p.1 p.2)
    (hout : Measurable A.output) (m n : ℕ) (h : t * m ≤ n) :
    PrivLearn.Generic.IsDP (fun z : Fin n → Dom => simOutputLaw A b ε m h z) ε := by
  have := laplace_sigmaFinite (2 * b / ε)
  intro z z' ⟨istar, _, hsame⟩ S hS
  have hmeasT : ∀ z : Fin n → Dom,
      Measurable fun η : Fin t → Fin m → ℝ => A.output (simTranscript A m h z η) := by
    intro z
    simp_rw [simTranscript_eq]
    exact hout.comp (measurable_pi_lambda _ fun k =>
      (measurable_ans A m hq k.1 k.2).comp (measurable_blocks_noise h z))
  unfold simOutputLaw
  rw [Measure.map_apply (hmeasT z) hS, Measure.map_apply (hmeasT z') hS]
  have hE : ∀ z : Fin n → Dom,
      MeasurableSet ((fun η => A.output (simTranscript A m h z η)) ⁻¹' S) :=
    fun z => hmeasT z hS
  by_cases hblk : ∃ k i, blockIdx h k i = istar
  · obtain ⟨k₀, i₀, hk⟩ := hblk
    subst hk
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by have := k₀.2; omega⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := i₀.2; omega⟩
    unfold noiseLaw
    refine pi_le_of_section _ k₀ (hE z) (hE z') _ fun r => ?_
    refine pi_le_of_section _ i₀ ((measurable_insertNth' k₀ r) (hE z))
      ((measurable_insertNth' k₀ r) (hE z')) _ fun q => ?_
    set p := pre A (m' + 1) (blocks h z (Yf k₀ i₀ r q 0)) k₀
    set δ := A.query k₀ p (z (blockIdx h k₀ i₀)) - A.query k₀ p (z' (blockIdx h k₀ i₀)) with hδdef
    have hcoup := shift_coupling A h z z' k₀ i₀ hsame r q δ hδdef
    have hδ : |δ| ≤ 2 * b := by
      rw [hδdef]
      calc _ ≤ |A.query k₀ p (z (blockIdx h k₀ i₀))| + |A.query k₀ p (z' (blockIdx h k₀ i₀))| :=
            abs_sub _ _
        _ ≤ b + b := add_le_add (hqb _ _ _) (hqb _ _ _)
        _ = 2 * b := by ring
    have hX : MeasurableSet {x | Yf k₀ i₀ r q x ∈
        (fun η => A.output (simTranscript A (m' + 1) h z' η)) ⁻¹' S} :=
      (measurable_Yf k₀ i₀ r q) (hE z')
    have hset : {x | Yf k₀ i₀ r q x ∈ (fun η => A.output (simTranscript A (m' + 1) h z η)) ⁻¹' S} =
        {x | x + δ ∈ {x | Yf k₀ i₀ r q x ∈
          (fun η => A.output (simTranscript A (m' + 1) h z' η)) ⁻¹' S}} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage]
      rw [hcoup x]
    show PrivLearn.Generic.laplace (2 * b / ε)
        {x | Yf k₀ i₀ r q x ∈ (fun η => A.output (simTranscript A (m' + 1) h z η)) ⁻¹' S} ≤ _ *
      PrivLearn.Generic.laplace (2 * b / ε)
        {x | Yf k₀ i₀ r q x ∈ (fun η => A.output (simTranscript A (m' + 1) h z' η)) ⁻¹' S}
    rw [hset]
    exact laplace_shift b ε hb hε δ hδ _ hX
  · push Not at hblk
    have heq : ∀ η, simTranscript A m h z η = simTranscript A m h z' η := by
      intro η
      rw [simTranscript_eq, simTranscript_eq]
      have : blocks h z η = blocks h z' η := by
        funext k
        simp only [blocks]
        congr 1
        funext i
        exact hsame _ (hblk k i)
      rw [this]
    simp only [heq]
    exact le_mul_of_one_le_left bot_le (ENNReal.one_le_ofReal.2 (Real.one_le_exp hε.le))

end LSAux
namespace LSAux

open MeasureTheory PrivLearn.LocalSim Set

variable {Dom Out : Type} [MeasurableSpace Dom]

/-- The data blocks of a database, flattened over `(query, position)`. -/
def flatBlocks {t m n : ℕ} (h : t * m ≤ n) (z : Fin n → Dom) : Fin t × Fin m → Dom :=
  fun x => z (blockIdx h x.1 x.2)

/-- The data blocks of a database. -/
def dataBlocks {t m n : ℕ} (h : t * m ≤ n) (z : Fin n → Dom) : Fin t → Fin m → Dom :=
  fun k i => z (blockIdx h k i)

lemma measurable_flatBlocks {t m n : ℕ} (h : t * m ≤ n) :
    Measurable (flatBlocks (Dom := Dom) h) :=
  measurable_pi_lambda _ fun x => measurable_pi_apply _

lemma measurable_dataBlocks {t m n : ℕ} (h : t * m ≤ n) :
    Measurable (dataBlocks (Dom := Dom) h) :=
  measurable_pi_lambda _ fun k => measurable_pi_lambda _ fun i => measurable_pi_apply _

lemma measurable_uncurry' {t m : ℕ} :
    Measurable fun f : Fin t → Fin m → Dom => fun x : Fin t × Fin m => f x.1 x.2 :=
  measurable_pi_lambda _ fun x => (measurable_pi_apply x.2).comp (measurable_pi_apply x.1)

lemma measurable_curry' {t m : ℕ} :
    Measurable fun f : Fin t × Fin m → Dom => fun k : Fin t => fun i : Fin m => f (k, i) :=
  measurable_pi_lambda _ fun k => measurable_pi_lambda _ fun i => measurable_pi_apply _

/-- The blocks are i.i.d.: the flat law. -/
lemma map_flatBlocks {t m n : ℕ} (h : t * m ≤ n) (P : Measure Dom) [IsProbabilityMeasure P] :
    (Measure.pi fun _ : Fin n => P).map (flatBlocks h) =
      Measure.pi fun _ : Fin t × Fin m => P := by
  classical
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (measurable_flatBlocks h) (MeasurableSet.univ_pi hs)]
  set s' : Fin n → Set Dom := fun j => {u | ∀ x : Fin t × Fin m, blockIdx h x.1 x.2 = j → u ∈ s x}
  have hpre : flatBlocks h ⁻¹' univ.pi s = univ.pi s' := by
    ext z
    simp only [mem_preimage, mem_univ_pi, flatBlocks, s', mem_ofPred_eq]
    constructor
    · intro hz j x hx
      rw [← hx]
      exact hz x
    · intro hz x
      exact hz _ x rfl
  rw [hpre, Measure.pi_pi]
  have hinj : Function.Injective fun x : Fin t × Fin m => blockIdx h x.1 x.2 :=
    fun x y he => Prod.ext (blockIdx_inj h he).1 (blockIdx_inj h he).2
  have hval : ∀ x : Fin t × Fin m, s' (blockIdx h x.1 x.2) = s x := by
    intro x
    ext u
    simp only [s', mem_ofPred_eq]
    constructor
    · intro hu; exact hu x rfl
    · intro hu y hy
      rw [hinj hy]
      exact hu
  rw [← Finset.prod_subset (Finset.subset_univ
      (Finset.univ.image fun x : Fin t × Fin m => blockIdx h x.1 x.2)),
    Finset.prod_image fun x _ y _ he => hinj he]
  · exact Finset.prod_congr rfl fun x _ => by rw [hval]
  · intro j _ hj
    have : s' j = univ := by
      ext u
      simp only [s', mem_ofPred_eq, mem_univ, iff_true]
      intro x hx
      exact absurd (Finset.mem_image.2 ⟨x, Finset.mem_univ _, hx⟩) hj
    rw [this, measure_univ]

lemma map_uncurry_pi {t m : ℕ} (P : Measure Dom) [IsProbabilityMeasure P] :
    (Measure.pi fun _ : Fin t => Measure.pi fun _ : Fin m => P).map
        (fun f : Fin t → Fin m → Dom => fun x : Fin t × Fin m => f x.1 x.2) =
      Measure.pi fun _ : Fin t × Fin m => P := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply measurable_uncurry' (MeasurableSet.univ_pi hs)]
  have hpre : (fun f : Fin t → Fin m → Dom => fun x : Fin t × Fin m => f x.1 x.2) ⁻¹'
      univ.pi s = univ.pi fun k => univ.pi fun i => s (k, i) := by
    ext f
    simp only [mem_preimage, mem_univ_pi]
    exact ⟨fun hf k i => hf (k, i), fun hf x => hf x.1 x.2⟩
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [← Finset.prod_product']
  rfl

/-- The blocks are i.i.d.: the nested law. -/
lemma map_dataBlocks {t m n : ℕ} (h : t * m ≤ n) (P : Measure Dom) [IsProbabilityMeasure P] :
    (Measure.pi fun _ : Fin n => P).map (dataBlocks h) =
      Measure.pi fun _ : Fin t => Measure.pi fun _ : Fin m => P := by
  have e1 : dataBlocks (Dom := Dom) h =
      (fun f : Fin t × Fin m → Dom => fun k : Fin t => fun i : Fin m => f (k, i)) ∘
        flatBlocks h := rfl
  have e2 : (fun f : Fin t × Fin m → Dom => fun k : Fin t => fun i : Fin m => f (k, i)) ∘
      (fun f : Fin t → Fin m → Dom => fun x : Fin t × Fin m => f x.1 x.2) = id := rfl
  rw [e1, ← Measure.map_map measurable_curry' (measurable_flatBlocks h), map_flatBlocks h P,
    ← map_uncurry_pi P, Measure.map_map measurable_curry' measurable_uncurry', e2, Measure.map_id]

/-- The law of the block data of the simulation: `t` i.i.d. copies of `P^m ⊗ Lap^m`. -/
lemma map_blocks {t m n : ℕ} (h : t * m ≤ n) (P : Measure Dom) [IsProbabilityMeasure P]
    (b ε : ℝ) :
    ((Measure.pi fun _ : Fin n => P).prod (noiseLaw t m b ε)).map
        (fun p => blocks h p.1 p.2) =
      Measure.pi fun _ : Fin t =>
        (Measure.pi fun _ : Fin m => P).prod
          (Measure.pi fun _ : Fin m => PrivLearn.Generic.laplace (2 * b / ε)) := by
  have := laplace_sigmaFinite (2 * b / ε)
  have : SFinite (noiseLaw t m b ε) := by unfold noiseLaw; infer_instance
  have hmp := measurePreserving_arrowProdEquivProdArrow (Fin m → Dom) (Fin m → ℝ) (Fin t)
    (fun _ => Measure.pi fun _ : Fin m => P)
    (fun _ => Measure.pi fun _ : Fin m => PrivLearn.Generic.laplace (2 * b / ε))
  have e1 : (fun p : (Fin n → Dom) × (Fin t → Fin m → ℝ) => blocks h p.1 p.2) =
      (MeasurableEquiv.arrowProdEquivProdArrow (Fin m → Dom) (Fin m → ℝ) (Fin t)).symm ∘
        Prod.map (dataBlocks h) id := rfl
  rw [e1, ← Measure.map_map (MeasurableEquiv.measurable _)
    ((measurable_dataBlocks h).prodMap measurable_id),
    ← Measure.map_prod_map _ _ (measurable_dataBlocks h) measurable_id, map_dataBlocks h P,
    Measure.map_id]
  exact hmp.symm.map_eq

/-- The failure event of query `k`, in terms of the block data. -/
def badW {t : ℕ} (A : SQAlg Dom Out t) (m : ℕ) (P : Measure Dom) (τ : ℝ) (k : Fin t) :
    Set (Fin t → Blk Dom m) :=
  {D | τ < |ans A m D k.1 k.2 - ∫ u, A.query k (pre A m D k) u ∂P|}

lemma measurableSet_badW {t : ℕ} (A : SQAlg Dom Out t) (m : ℕ)
    (hq : ∀ k : Fin t, Measurable fun p : (Fin k → ℝ) × Dom => A.query k p.1 p.2)
    (P : Measure Dom) [IsProbabilityMeasure P] (τ : ℝ) (k : Fin t) :
    MeasurableSet (badW A m P τ k) := by
  have hint : Measurable fun a : Fin k → ℝ => ∫ u, A.query k a u ∂P :=
    ((hq k).stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  exact measurableSet_lt measurable_const
    (((measurable_ans A m hq k.1 k.2).sub (hint.comp (measurable_pre A m hq k))).abs)

/-- Lemma 5.6 in complement form: the failure probability of one block is at most `β`. -/
lemma block_fail (c : ℝ)
    (h56 : ∀ (Dom : Type) [MeasurableSpace Dom] (P : Measure Dom) [IsProbabilityMeasure P]
      (g : Dom → ℝ) (b ε τ β : ℝ) (n : ℕ),
      Measurable g → (∀ u, |g u| ≤ b) →
      0 < b → 0 < ε → ε ≤ 1 → 0 < τ → ε * τ ≤ 4 * b → 0 < β → β < 1 →
      c * Real.log (1 / β) * b ^ 2 / (ε ^ 2 * τ ^ 2) ≤ n →
      ENNReal.ofReal (1 - β) ≤
        ((Measure.pi fun _ : Fin n => P).prod
            (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace (2 * b / ε)))
          {p | |avgResp g p.1 p.2 - ∫ x, g x ∂P| ≤ τ})
    (P : Measure Dom) [IsProbabilityMeasure P] (g : Dom → ℝ) (b ε τ β : ℝ) (m : ℕ)
    (hg : Measurable g) (hgb : ∀ u, |g u| ≤ b) (hb : 0 < b) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hτ : 0 < τ) (hετ : ε * τ ≤ 4 * b) (hβ : 0 < β) (hβ1 : β < 1)
    (hm : c * Real.log (1 / β) * b ^ 2 / (ε ^ 2 * τ ^ 2) ≤ m) :
    ((Measure.pi fun _ : Fin m => P).prod
        (Measure.pi fun _ : Fin m => PrivLearn.Generic.laplace (2 * b / ε)))
      {p | τ < |avgResp g p.1 p.2 - ∫ x, g x ∂P|} ≤ ENNReal.ofReal β := by
  have := laplace_isProb' (2 * b / ε) (by positivity)
  set ν := (Measure.pi fun _ : Fin m => P).prod
    (Measure.pi fun _ : Fin m => PrivLearn.Generic.laplace (2 * b / ε))
  have hgood := h56 Dom P g b ε τ β m hg hgb hb hε hε1 hτ hετ hβ hβ1 hm
  have hmeas : MeasurableSet {p : (Fin m → Dom) × (Fin m → ℝ) |
      |avgResp g p.1 p.2 - ∫ x, g x ∂P| ≤ τ} := by
    refine measurableSet_le ?_ measurable_const
    refine ((Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _).sub
      measurable_const).abs
    exact (hg.comp ((measurable_pi_apply i).comp measurable_fst)).add
      ((measurable_pi_apply i).comp measurable_snd)
  have hcompl : {p : (Fin m → Dom) × (Fin m → ℝ) | τ < |avgResp g p.1 p.2 - ∫ x, g x ∂P|} =
      {p | |avgResp g p.1 p.2 - ∫ x, g x ∂P| ≤ τ}ᶜ := by
    ext p; simp [not_le]
  rw [hcompl]
  have hsum := measure_add_measure_compl (μ := ν) hmeas
  rw [measure_univ] at hsum
  have h1 : ENNReal.ofReal (1 - β) + ENNReal.ofReal β = 1 := by
    rw [← ENNReal.ofReal_add (by linarith) hβ.le]; simp
  have h2 : ν {p | |avgResp g p.1 p.2 - ∫ x, g x ∂P| ≤ τ}ᶜ + ENNReal.ofReal (1 - β) ≤
      ENNReal.ofReal β + ENNReal.ofReal (1 - β) := by
    calc _ ≤ ν {p | |avgResp g p.1 p.2 - ∫ x, g x ∂P| ≤ τ}ᶜ +
          ν {p | |avgResp g p.1 p.2 - ∫ x, g x ∂P| ≤ τ} := add_le_add_right hgood _
      _ = 1 := by rw [add_comm]; exact hsum
      _ = _ := by rw [add_comm]; exact h1.symm
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h2

/-- The failure probability of query `k` under i.i.d. blocks. -/
lemma badW_le (c : ℝ)
    (h56 : ∀ (Dom : Type) [MeasurableSpace Dom] (P : Measure Dom) [IsProbabilityMeasure P]
      (g : Dom → ℝ) (b ε τ β : ℝ) (n : ℕ),
      Measurable g → (∀ u, |g u| ≤ b) →
      0 < b → 0 < ε → ε ≤ 1 → 0 < τ → ε * τ ≤ 4 * b → 0 < β → β < 1 →
      c * Real.log (1 / β) * b ^ 2 / (ε ^ 2 * τ ^ 2) ≤ n →
      ENNReal.ofReal (1 - β) ≤
        ((Measure.pi fun _ : Fin n => P).prod
            (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace (2 * b / ε)))
          {p | |avgResp g p.1 p.2 - ∫ x, g x ∂P| ≤ τ})
    {t' : ℕ} (A : SQAlg Dom Out (t' + 1)) (m : ℕ) (b ε τ β : ℝ)
    (hq : ∀ k : Fin (t' + 1), Measurable fun p : (Fin k → ℝ) × Dom => A.query k p.1 p.2)
    (hqb : ∀ (k : Fin (t' + 1)) (a : Fin k → ℝ) (u : Dom), |A.query k a u| ≤ b)
    (P : Measure Dom) [IsProbabilityMeasure P] (hb : 0 < b) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hτ : 0 < τ) (hετ : ε * τ ≤ 4 * b) (hβ : 0 < β) (hβ1 : β < 1)
    (hm : c * Real.log (1 / β) * b ^ 2 / (ε ^ 2 * τ ^ 2) ≤ m) (k : Fin (t' + 1)) :
    (Measure.pi fun _ : Fin (t' + 1) =>
        (Measure.pi fun _ : Fin m => P).prod
          (Measure.pi fun _ : Fin m => PrivLearn.Generic.laplace (2 * b / ε)))
      (badW A m P τ k) ≤ ENNReal.ofReal β := by
  have := laplace_isProb' (2 * b / ε) (by positivity)
  set ν := (Measure.pi fun _ : Fin m => P).prod
    (Measure.pi fun _ : Fin m => PrivLearn.Generic.laplace (2 * b / ε))
  have hle := pi_le_of_section ν k (measurableSet_badW A m hq P τ k) MeasurableSet.univ
    (ENNReal.ofReal β) fun r => ?_
  · simpa using hle
  simp only [mem_univ, ofPred_true, measure_univ, mul_one]
  rcases isEmpty_or_nonempty (Blk Dom m) with hE | hne
  · rw [Set.eq_empty_of_isEmpty {x : Blk Dom m | _}, measure_empty]
    exact bot_le
  obtain ⟨x₀⟩ := hne
  set p := pre A m (Fin.insertNth (α := fun _ => Blk Dom m) k x₀ r) k
  have hsec : {x : Blk Dom m | Fin.insertNth (α := fun _ => Blk Dom m) k x r ∈ badW A m P τ k} =
      {x | τ < |avgResp (A.query k p) x.1 x.2 - ∫ u, A.query k p u ∂P|} := by
    ext x
    have hp : pre A m (Fin.insertNth (α := fun _ => Blk Dom m) k x r) k = p := by
      apply pre_congr
      intro j hj
      exact insertNth_ne k x x₀ r j (fun e => by rw [e] at hj; exact lt_irrefl _ hj)
    simp only [badW, mem_ofPred_eq]
    rw [ans_eq]
    simp only [Fin.eta, Fin.insertNth_apply_same]
    rw [hp]
    rfl
  rw [hsec]
  exact block_fail c h56 P (A.query k p) b ε τ β m
    ((hq k).comp (measurable_const.prodMk measurable_id)) (hqb k p) hb hε hε1 hτ hετ hβ hβ1 hm

end LSAux
namespace LSAux

open MeasureTheory PrivLearn.LocalSim Set

variable {Dom Out : Type} [MeasurableSpace Dom]

/-- Part 2 of Theorem 5.7: union bound over the queries, each failing with probability at most
`β/t` by Lemma 5.6 applied to its fresh block. -/
lemma accuracy (c : ℝ)
    (h56 : ∀ (Dom : Type) [MeasurableSpace Dom] (P : Measure Dom) [IsProbabilityMeasure P]
      (g : Dom → ℝ) (b ε τ β : ℝ) (n : ℕ),
      Measurable g → (∀ u, |g u| ≤ b) →
      0 < b → 0 < ε → ε ≤ 1 → 0 < τ → ε * τ ≤ 4 * b → 0 < β → β < 1 →
      c * Real.log (1 / β) * b ^ 2 / (ε ^ 2 * τ ^ 2) ≤ n →
      ENNReal.ofReal (1 - β) ≤
        ((Measure.pi fun _ : Fin n => P).prod
            (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace (2 * b / ε)))
          {p | |avgResp g p.1 p.2 - ∫ x, g x ∂P| ≤ τ})
    {t : ℕ} (A : SQAlg Dom Out t) (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε)
    (hqb : ∀ (k : Fin t) (a : Fin k → ℝ) (u : Dom), |A.query k a u| ≤ b)
    (hq : ∀ k : Fin t, Measurable fun p : (Fin k → ℝ) × Dom => A.query k p.1 p.2)
    (τ β : ℝ) (hε1 : ε ≤ 1) (hτ : 0 < τ) (hετ : ε * τ ≤ 4 * b) (hβ : 0 < β) (hβ1 : β < 1)
    (htol : ∀ (k : Fin t) (a : Fin k → ℝ), τ ≤ A.tol k a)
    (P : Measure Dom) [IsProbabilityMeasure P] (m n : ℕ) (h : t * m ≤ n)
    (hm : c * Real.log (t / β) * b ^ 2 / (ε ^ 2 * τ ^ 2) ≤ m) :
    ((Measure.pi fun _ : Fin n => P).prod (noiseLaw t m b ε))
        {p | ¬ A.IsValidTranscript P (simTranscript A m h p.1 p.2)}
      ≤ ENNReal.ofReal β := by
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · have : {p : (Fin n → Dom) × (Fin 0 → Fin m → ℝ) |
        ¬ A.IsValidTranscript P (simTranscript A m h p.1 p.2)} = ∅ := by
      ext p
      simp [SQAlg.IsValidTranscript]
    rw [this, measure_empty]
    exact bot_le
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  set T : ℝ := ((t' + 1 : ℕ) : ℝ) with hT
  have hTpos : 0 < T := by rw [hT]; positivity
  have hT1 : 1 ≤ T := by rw [hT]; exact_mod_cast Nat.succ_pos t'
  have hβ' : 0 < β / T := div_pos hβ hTpos
  have hβ'1 : β / T < 1 := by rw [div_lt_one hTpos]; linarith
  have hm' : c * Real.log (1 / (β / T)) * b ^ 2 / (ε ^ 2 * τ ^ 2) ≤ m := by
    rwa [one_div_div]
  set Ψ : (Fin n → Dom) × (Fin (t' + 1) → Fin m → ℝ) → (Fin (t' + 1) → Blk Dom m) :=
    fun p => blocks h p.1 p.2 with hΨdef
  have hΨ : Measurable Ψ :=
    measurable_pi_lambda _ fun k =>
      (measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp measurable_fst).prodMk
        ((measurable_pi_apply k).comp measurable_snd)
  have hsub : {p : (Fin n → Dom) × (Fin (t' + 1) → Fin m → ℝ) |
      ¬ A.IsValidTranscript P (simTranscript A m h p.1 p.2)} ⊆
      Ψ ⁻¹' ⋃ k, badW A m P τ k := by
    intro p hp
    simp only [mem_ofPred_eq, SQAlg.IsValidTranscript, not_forall] at hp
    obtain ⟨k, hk⟩ := hp
    simp only [mem_preimage, mem_iUnion]
    refine ⟨k, ?_⟩
    unfold IsSQAnswer at hk
    rw [not_le, simTranscript_eq] at hk
    have hpre : answerPrefix (fun k : Fin (t' + 1) => ans A m (blocks h p.1 p.2) k.1 k.2) k =
        pre A m (blocks h p.1 p.2) k := by
      funext j
      rfl
    rw [hpre] at hk
    exact lt_of_le_of_lt (htol k _) hk
  calc _ ≤ ((Measure.pi fun _ : Fin n => P).prod (noiseLaw (t' + 1) m b ε))
          (Ψ ⁻¹' ⋃ k, badW A m P τ k) := measure_mono hsub
    _ ≤ (((Measure.pi fun _ : Fin n => P).prod (noiseLaw (t' + 1) m b ε)).map Ψ)
          (⋃ k, badW A m P τ k) := Measure.le_map_apply hΨ.aemeasurable _
    _ = (Measure.pi fun _ : Fin (t' + 1) =>
          (Measure.pi fun _ : Fin m => P).prod
            (Measure.pi fun _ : Fin m => PrivLearn.Generic.laplace (2 * b / ε)))
          (⋃ k, badW A m P τ k) := by rw [hΨdef, map_blocks h P b ε]
    _ ≤ ∑ k, (Measure.pi fun _ : Fin (t' + 1) =>
          (Measure.pi fun _ : Fin m => P).prod
            (Measure.pi fun _ : Fin m => PrivLearn.Generic.laplace (2 * b / ε)))
          (badW A m P τ k) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _k : Fin (t' + 1), ENNReal.ofReal (β / T) :=
        Finset.sum_le_sum fun k _ =>
          badW_le c h56 A m b ε τ (β / T) hq hqb P hb hε hε1 hτ hετ hβ' hβ'1 hm' k
    _ = ENNReal.ofReal β := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ← hT]
        congr 1
        field_simp

end LSAux

open MeasureTheory PrivLearn.LocalSim LSAux

theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Dom Out : Type) [MeasurableSpace Dom] [MeasurableSpace Out] (t : ℕ) (A : SQAlg Dom Out t)
        (b ε : ℝ),
        0 < b → 0 < ε →
        (∀ (k : Fin t) (a : Fin k → ℝ) (u : Dom), |A.query k a u| ≤ b) →
        (∀ k : Fin t, Measurable fun p : (Fin k → ℝ) × Dom => A.query k p.1 p.2) →
        -- privacy (for every ε > 0, every block size and every database)
        (Measurable A.output →
          ∀ (m n : ℕ) (h : t * m ≤ n),
            PrivLearn.Generic.IsDP (fun z : Fin n → Dom => simOutputLaw A b ε m h z) ε) ∧
        -- accuracy
        (∀ (τ β : ℝ), ε ≤ 1 → 0 < τ → ε * τ ≤ 4 * b → 0 < β → β < 1 →
          (∀ (k : Fin t) (a : Fin k → ℝ), τ ≤ A.tol k a) →
          ∀ (P : Measure Dom) [IsProbabilityMeasure P] (m n : ℕ) (h : t * m ≤ n),
            c * Real.log (t / β) * b ^ 2 / (ε ^ 2 * τ ^ 2) ≤ m →
            ((Measure.pi fun _ : Fin n => P).prod (noiseLaw t m b ε))
                {p | ¬ A.IsValidTranscript P (simTranscript A m h p.1 p.2)}
              ≤ ENNReal.ofReal β) := by
  obtain ⟨c, hc, h56⟩ := lemma_5_6
  refine ⟨c, hc, ?_⟩
  intro Dom Out _ _ t A b ε hb hε hqb hq
  refine ⟨fun hout m n h => privacy A b ε hb hε hqb hq hout m n h, ?_⟩
  intro τ β hε1 hτ hετ hβ hβ1 htol P _ m n h hm
  exact accuracy c h56 A b ε hb hε hqb hq τ β hε1 hτ hετ hβ hβ1 htol P m n h hm
