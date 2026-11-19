-- Prove2me | solution 1 for PrivLearn.LocalSim.lemma_5_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T01:57:25.927143+00:00
-- url     : https://prove2.me/submissions/6a5b2763-74c2-42b4-a63c-d3dd5ef72486

import Mathlib
import Definitions.Def_PrivLearn_LocalSim_Privacy
import Definitions.Def_PrivLearn_LocalSim_Simulation
import Theorems.Thm_PrivLearn_LocalSim_hoeffding_display
import Theorems.Thm_PrivLearn_LocalSim_laplace_average

open MeasureTheory Set

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

namespace L56
lemma laplace_mgf_le (s t : ℝ) (hs : 0 < s) (ht : |t| ≤ 1 / (2 * s)) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (t * x)) ∂(PrivLearn.Generic.laplace s)) ≤
      ENNReal.ofReal (Real.exp (2 * s ^ 2 * t ^ 2)) := by
  obtain ⟨ht_lo, ht_hi⟩ := abs_le.mp ht
  have hs_inv : 0 < 1 / s := by positivity
  have h2s_lt : 1 / (2 * s) < 1 / s := by
    rw [div_lt_div_iff₀ (by positivity) hs]
    linarith
  set a₁ := t + 1 / s
  set a₂ := t - 1 / s
  have ha₁ : 0 < a₁ := by dsimp [a₁]; linarith
  have ha₂ : a₂ < 0 := by dsimp [a₂]; linarith
  have hm1 : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-|x| / s) / (2 * s))) := by
    fun_prop
  have hm2 : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (t * x))) := by
    fun_prop
  unfold PrivLearn.Generic.laplace
  rw [lintegral_withDensity_eq_lintegral_mul volume hm1 hm2]
  have h_prod : (fun x : ℝ => ENNReal.ofReal (Real.exp (-|x| / s) / (2 * s)) *
      ENNReal.ofReal (Real.exp (t * x))) =
      fun x : ℝ => ENNReal.ofReal (1 / (2 * s)) *
        ENNReal.ofReal (Real.exp (t * x - |x| / s)) := by
    ext x
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [div_eq_inv_mul, mul_assoc, ← Real.exp_add]
    ring_nf
  change (∫⁻ a, (fun x : ℝ => ENNReal.ofReal (Real.exp (-|x| / s) / (2 * s)) *
    ENNReal.ofReal (Real.exp (t * x))) a) ≤ _
  rw [h_prod, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_add_compl _ measurableSet_Iic, compl_Iic]
  have h_iic : (∫⁻ x in Iic (0 : ℝ), ENNReal.ofReal (Real.exp (t * x - |x| / s))) =
      ENNReal.ofReal (1 / a₁) := by
    have heq : EqOn (fun x : ℝ => ENNReal.ofReal (Real.exp (t * x - |x| / s)))
        (fun x : ℝ => ENNReal.ofReal (Real.exp (a₁ * x))) (Iic 0) := by
      intro x hx
      dsimp [a₁]
      rw [abs_of_nonpos hx]
      ring_nf
    rw [setLIntegral_congr_fun measurableSet_Iic heq,
      ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Iic ha₁ 0)
        (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le),
      integral_exp_mul_Iic ha₁ 0]
    simp
  have h_ioi : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (t * x - |x| / s))) =
      ENNReal.ofReal (-1 / a₂) := by
    have heq : EqOn (fun x : ℝ => ENNReal.ofReal (Real.exp (t * x - |x| / s)))
        (fun x : ℝ => ENNReal.ofReal (Real.exp (a₂ * x))) (Ioi 0) := by
      intro x hx
      dsimp [a₂]
      rw [abs_of_pos hx]
      ring_nf
    rw [setLIntegral_congr_fun measurableSet_Ioi heq,
      ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Ioi ha₂ 0)
        (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le),
      integral_exp_mul_Ioi ha₂ 0]
    simp [neg_div]
  rw [h_iic, h_ioi]
  have ha₂_pos : 0 < -1 / a₂ := div_pos_of_neg_of_neg (by norm_num) ha₂
  rw [← ENNReal.ofReal_add (by positivity) ha₂_pos.le,
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hst : |s * t| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hs]
    calc s * |t| ≤ s * (1 / (2 * s)) := mul_le_mul_of_nonneg_left ht hs.le
      _ = 1 / 2 := by field_simp
  have hst_sq : s ^ 2 * t ^ 2 ≤ 1 / 4 := by
    obtain ⟨h1, h2⟩ := abs_le.mp hst
    nlinarith
  have h_denom : 0 < 1 - s ^ 2 * t ^ 2 := by linarith
  have h_alg : 1 / (2 * s) * (1 / a₁ + -1 / a₂) = 1 / (1 - s ^ 2 * t ^ 2) := by
    dsimp [a₁, a₂]
    have ha₁_ne : t + 1 / s ≠ 0 := ha₁.ne'
    have ha₂_ne : t - 1 / s ≠ 0 := ha₂.ne
    have hs_ne : s ≠ 0 := hs.ne'
    have hd_ne : 1 - s ^ 2 * t ^ 2 ≠ 0 := h_denom.ne'
    have h1 : t + 1 / s = (s * t + 1) / s := by field_simp
    have h2 : t - 1 / s = (s * t - 1) / s := by field_simp
    have hst1 : s * t + 1 ≠ 0 := by obtain ⟨_, _⟩ := abs_le.mp hst; linarith
    have hst2 : s * t - 1 ≠ 0 := by obtain ⟨_, _⟩ := abs_le.mp hst; linarith
    rw [h1, h2]
    field_simp
    ring
  rw [h_alg]
  calc 1 / (1 - s ^ 2 * t ^ 2) ≤ 1 + 2 * s ^ 2 * t ^ 2 := by
        rw [div_le_iff₀ h_denom]
        nlinarith [sq_nonneg (s * t)]
    _ ≤ Real.exp (2 * s ^ 2 * t ^ 2) := by
        linarith [Real.add_one_le_exp (2 * s ^ 2 * t ^ 2)]

lemma lintegral_pi_prod (μ : Measure ℝ) [SigmaFinite μ] (g : ℝ → ENNReal)
    (hg : Measurable g) :
    ∀ n : ℕ, (∫⁻ η : Fin n → ℝ, (∏ i : Fin n, g (η i)) ∂(Measure.pi fun _ : Fin n => μ)) =
      (∫⁻ x : ℝ, g x ∂μ) ^ n
  | 0 => by simp [Measure.pi_empty_univ]
  | m + 1 => by
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    have hmp : (μ.prod (Measure.pi fun _ : Fin m => μ)).map e.symm =
        Measure.pi (fun _ : Fin (m + 1) => μ) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0).symm.map_eq
    have hm_prod : Measurable (fun η : Fin (m + 1) → ℝ => ∏ i : Fin (m + 1), g (η i)) :=
      Finset.measurable_prod Finset.univ fun i _ => hg.comp (measurable_pi_apply i)
    rw [← hmp, lintegral_map hm_prod e.symm.measurable]
    have h_split : (fun p : ℝ × (Fin m → ℝ) => ∏ i : Fin (m + 1), g (e.symm p i)) =
        fun p : ℝ × (Fin m → ℝ) => g p.1 * ∏ j : Fin m, g (p.2 j) := by
      ext ⟨x, y⟩
      have he : e.symm (x, y) = (0 : Fin (m + 1)).insertNth x y := rfl
      rw [he, Fin.prod_univ_succAbove _ 0, Fin.insertNth_apply_same]
      simp
    rw [h_split]
    have hm_prod_m : Measurable (fun y : Fin m → ℝ => ∏ j : Fin m, g (y j)) :=
      Finset.measurable_prod Finset.univ fun j _ => hg.comp (measurable_pi_apply j)
    rw [lintegral_prod_mul hg.aemeasurable hm_prod_m.aemeasurable,
      lintegral_pi_prod μ g hg m, pow_succ']

lemma laplace_sum_tail (s t a : ℝ) (hs : 0 < s) (ht : |t| ≤ 1 / (2 * s)) (n : ℕ) :
    (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace s)
      {η : Fin n → ℝ | a ≤ t * ∑ i, η i} ≤
      ENNReal.ofReal (Real.exp ((n : ℝ) * (2 * s ^ 2 * t ^ 2) - a)) := by
  set μ : Measure ℝ := PrivLearn.Generic.laplace s
  have : SigmaFinite μ := by
    dsimp [μ, PrivLearn.Generic.laplace]
    infer_instance
  set P : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => μ)
  set f : (Fin n → ℝ) → ENNReal := fun η => ENNReal.ofReal (Real.exp (t * ∑ i, η i))
  have hf_meas : Measurable f := by
    refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
    exact measurable_const.mul (Finset.measurable_sum Finset.univ fun i _ => measurable_pi_apply i)
  have h_sub : {η : Fin n → ℝ | a ≤ t * ∑ i, η i} ⊆
      {η : Fin n → ℝ | ENNReal.ofReal (Real.exp a) ≤ f η} := by
    intro η hη
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hη)
  have h_markov := mul_meas_ge_le_lintegral (μ := P) hf_meas (ENNReal.ofReal (Real.exp a))
  have h_prod_eq : ∀ η : Fin n → ℝ, f η = ∏ i : Fin n, ENNReal.ofReal (Real.exp (t * η i)) := by
    intro η
    dsimp [f]
    rw [Finset.mul_sum, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  have h_lint : ∫⁻ η, f η ∂P ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * (2 * s ^ 2 * t ^ 2))) := by
    have hg_meas : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (t * x))) := by fun_prop
    rw [lintegral_congr h_prod_eq]
    dsimp [P]
    rw [lintegral_pi_prod μ _ hg_meas]
    calc (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (t * x)) ∂μ) ^ n
        ≤ (ENNReal.ofReal (Real.exp (2 * s ^ 2 * t ^ 2))) ^ n :=
          pow_le_pow_left' (laplace_mgf_le s t hs ht) n
      _ = ENNReal.ofReal ((Real.exp (2 * s ^ 2 * t ^ 2)) ^ n) :=
          (ENNReal.ofReal_pow (Real.exp_pos _).le n).symm
      _ = ENNReal.ofReal (Real.exp ((n : ℝ) * (2 * s ^ 2 * t ^ 2))) := by
          rw [← Real.exp_nat_mul]
  have h_le : ENNReal.ofReal (Real.exp a) * P {η : Fin n → ℝ | a ≤ t * ∑ i, η i} ≤
      ENNReal.ofReal (Real.exp ((n : ℝ) * (2 * s ^ 2 * t ^ 2))) :=
    (mul_le_mul_of_nonneg_left (measure_mono h_sub) zero_le).trans (h_markov.trans h_lint)
  have h_mul := mul_le_mul_of_nonneg_left h_le (zero_le : 0 ≤ ENNReal.ofReal (Real.exp (-a)))
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel,
    Real.exp_zero, ENNReal.ofReal_one, one_mul,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add] at h_mul
  rw [sub_eq_neg_add]
  exact h_mul

end L56

namespace L56

open MeasureTheory Set

/-- `∫⁻ ∏ g_i(η_i) d(μ^n) = ∏ ∫⁻ g_i dμ`. -/
lemma lintegral_pi_prod' (μ : Measure ℝ) [SigmaFinite μ] :
    ∀ (n : ℕ) (g : Fin n → ℝ → ENNReal), (∀ i, Measurable (g i)) →
      (∫⁻ η : Fin n → ℝ, (∏ i : Fin n, g i (η i)) ∂(Measure.pi fun _ : Fin n => μ)) =
        ∏ i, ∫⁻ x : ℝ, g i x ∂μ
  | 0, g, _ => by simp [Measure.pi_empty_univ]
  | m + 1, g, hg => by
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    have hmp : (μ.prod (Measure.pi fun _ : Fin m => μ)).map e.symm =
        Measure.pi (fun _ : Fin (m + 1) => μ) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0).symm.map_eq
    have hm_prod : Measurable (fun η : Fin (m + 1) → ℝ => ∏ i : Fin (m + 1), g i (η i)) :=
      Finset.measurable_prod Finset.univ fun i _ => (hg i).comp (measurable_pi_apply i)
    rw [← hmp, lintegral_map hm_prod e.symm.measurable]
    have h_split : (fun p : ℝ × (Fin m → ℝ) => ∏ i : Fin (m + 1), g i (e.symm p i)) =
        fun p : ℝ × (Fin m → ℝ) => g 0 p.1 * ∏ j : Fin m, g (Fin.succ j) (p.2 j) := by
      ext ⟨x, y⟩
      have he : e.symm (x, y) = (0 : Fin (m + 1)).insertNth x y := rfl
      rw [he, Fin.prod_univ_succ, Fin.insertNth_apply_same]
      congr 1
    rw [h_split]
    have hm_prod_m : Measurable (fun y : Fin m → ℝ => ∏ j : Fin m, g (Fin.succ j) (y j)) :=
      Finset.measurable_prod Finset.univ fun j _ => (hg _).comp (measurable_pi_apply j)
    rw [lintegral_prod_mul (hg 0).aemeasurable hm_prod_m.aemeasurable,
      lintegral_pi_prod' μ m (fun j => g (Fin.succ j)) (fun j => hg _), Fin.prod_univ_succ]

/-- The Laplace density. -/
noncomputable def dens (s : ℝ) (x : ℝ) : ENNReal := ENNReal.ofReal (Real.exp (-|x| / s) / (2 * s))

lemma measurable_dens (s : ℝ) : Measurable (dens s) := by unfold dens; fun_prop

lemma laplace_eq (s : ℝ) : PrivLearn.Generic.laplace s = volume.withDensity (dens s) := rfl

/-- Right tail: `Lap(s)(a, ∞) = e^{−a/s}/2` for `a ≥ 0`. -/
lemma laplace_Ioi (s a : ℝ) (hs : 0 < s) (ha : 0 ≤ a) :
    PrivLearn.Generic.laplace s (Ioi a) = ENNReal.ofReal (Real.exp (-a / s) / 2) := by
  rw [laplace_eq, withDensity_apply _ measurableSet_Ioi]
  have heq : EqOn (dens s) (fun x : ℝ => ENNReal.ofReal (1 / (2 * s)) *
      ENNReal.ofReal (Real.exp ((-(1 / s)) * x))) (Ioi a) := by
    intro x hx
    simp only [dens]
    rw [← ENNReal.ofReal_mul (by positivity), abs_of_pos (lt_of_le_of_lt ha hx)]
    congr 1
    ring_nf
  have ha₂ : -(1 / s) < 0 := by have : 0 < 1 / s := by positivity
                                linarith
  rw [setLIntegral_congr_fun measurableSet_Ioi heq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Ioi ha₂ a)
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le),
    integral_exp_mul_Ioi ha₂ a, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- Left tail: `Lap(s)(−∞, −a] = e^{−a/s}/2` for `a ≥ 0`. -/
lemma laplace_Iic (s a : ℝ) (hs : 0 < s) (ha : 0 ≤ a) :
    PrivLearn.Generic.laplace s (Iic (-a)) = ENNReal.ofReal (Real.exp (-a / s) / 2) := by
  rw [laplace_eq, withDensity_apply _ measurableSet_Iic]
  have heq : EqOn (dens s) (fun x : ℝ => ENNReal.ofReal (1 / (2 * s)) *
      ENNReal.ofReal (Real.exp ((1 / s) * x))) (Iic (-a)) := by
    intro x hx
    simp only [dens]
    have hx' : x ≤ 0 := le_trans (mem_Iic.1 hx) (by linarith)
    rw [← ENNReal.ofReal_mul (by positivity), abs_of_nonpos hx']
    congr 1
    ring_nf
  have ha₁ : 0 < 1 / s := by positivity
  rw [setLIntegral_congr_fun measurableSet_Iic heq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Iic ha₁ (-a))
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le),
    integral_exp_mul_Iic ha₁ (-a), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- The real bound for the cost of a shift. -/
noncomputable def Mb (u : ℝ) : ℝ := Real.exp u - 1 / 2 + Real.exp (-2 * u) / 2

lemma Mb_le_exp (u : ℝ) (hu : 0 ≤ u) : Mb u ≤ Real.exp u := by
  unfold Mb
  have : Real.exp (-2 * u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  linarith

lemma Mb_le_quad (u : ℝ) (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) : Mb u ≤ 1 + 3 * u ^ 2 := by
  unfold Mb
  have h1 := Real.exp_bound (x := u) (by rw [abs_of_nonneg hu]; linarith) (n := 2) (by norm_num)
  have h2 := Real.exp_bound (x := -2 * u) (by rw [abs_le]; constructor <;> linarith) (n := 2)
    (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at h1 h2
  rw [abs_le] at h1 h2
  rw [abs_of_nonneg hu] at h2
  have e : -2 * u = -(2 * u) := by ring
  rw [e]
  nlinarith [h1.2, h2.2]

/-- The cost `M(δ) = ∫ e^{(|x−δ| − |x|)/s} dLap(s)` of shifting one coordinate by `δ`. -/
lemma M_le (s δ : ℝ) (hs : 0 < s) :
    (∫⁻ x, ENNReal.ofReal (Real.exp ((|x - δ| - |x|) / s)) ∂PrivLearn.Generic.laplace s) ≤
      ENNReal.ofReal (Mb (|δ| / s)) := by
  have hprob := LSAux.laplace_isProb' s hs
  set u := |δ| / s with hu
  have hu0 : 0 ≤ u := by positivity
  -- the tail on which the exponent is `−u`
  set Tl : Set ℝ := if 0 ≤ δ then Ioi δ else Iic δ with hTl
  have hTm : MeasurableSet Tl := by rw [hTl]; split_ifs <;> measurability
  have hTlmass : PrivLearn.Generic.laplace s Tl = ENNReal.ofReal (Real.exp (-u) / 2) := by
    rw [hTl]
    split_ifs with hδ
    · rw [laplace_Ioi s δ hs hδ, hu, abs_of_nonneg hδ, neg_div]
    · have hδ' : δ < 0 := not_le.1 hδ
      have : Iic δ = Iic (-|δ|) := by rw [abs_of_neg hδ', neg_neg]
      rw [this, laplace_Iic s |δ| hs (abs_nonneg _), hu, neg_div]
  have hpt : ∀ x, ENNReal.ofReal (Real.exp ((|x - δ| - |x|) / s)) ≤
      Tl.indicator (fun _ => ENNReal.ofReal (Real.exp (-u))) x +
        Tlᶜ.indicator (fun _ => ENNReal.ofReal (Real.exp u)) x := by
    intro x
    by_cases hx : x ∈ Tl
    · rw [indicator_of_mem hx, indicator_of_notMem (by simpa using hx), add_zero]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.2
      rw [hu, ← neg_div]
      apply div_le_div_of_nonneg_right _ hs.le
      rw [hTl] at hx
      split_ifs at hx with hδ
      · have hx' : δ < x := hx
        rw [abs_of_nonneg (by linarith : 0 ≤ x - δ), abs_of_nonneg (by linarith : 0 ≤ x),
          abs_of_nonneg hδ]
        linarith
      · have hx' : x ≤ δ := hx
        have hδ' : δ < 0 := not_le.1 hδ
        rw [abs_of_nonpos (by linarith : x - δ ≤ 0), abs_of_nonpos (by linarith : x ≤ 0),
          abs_of_neg hδ']
        linarith
    · rw [indicator_of_notMem hx, indicator_of_mem (by simpa using hx), zero_add]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.2
      rw [hu]
      apply div_le_div_of_nonneg_right _ hs.le
      have := abs_sub_abs_le_abs_sub x δ
      have h2 : |x - δ| ≤ |x| + |δ| := abs_sub _ _
      linarith
  calc _ ≤ ∫⁻ x, (Tl.indicator (fun _ => ENNReal.ofReal (Real.exp (-u))) x +
        Tlᶜ.indicator (fun _ => ENNReal.ofReal (Real.exp u)) x) ∂PrivLearn.Generic.laplace s :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (Real.exp (-u)) * PrivLearn.Generic.laplace s Tl +
        ENNReal.ofReal (Real.exp u) * PrivLearn.Generic.laplace s Tlᶜ := by
        rw [lintegral_add_left (measurable_const.indicator hTm),
          lintegral_indicator_const hTm, lintegral_indicator_const hTm.compl]
    _ = ENNReal.ofReal (Mb u) := by
        rw [prob_compl_eq_one_sub hTm, hTlmass, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_sub _ (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)]
        · congr 1
          unfold Mb
          have e1 : Real.exp (-u) * Real.exp (-u) = Real.exp (-2 * u) := by
            rw [← Real.exp_add]; ring_nf
          have e2 : Real.exp u * Real.exp (-u) = 1 := by
            rw [← Real.exp_add]; simp
          nlinarith [e1, e2]
        · apply mul_nonneg (Real.exp_pos _).le
          have : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
          linarith

end L56
namespace L56

open MeasureTheory Set

/-- The density ratio of the shifted Laplace law. -/
noncomputable def rho (s δ : ℝ) (x : ℝ) : ENNReal :=
  ENNReal.ofReal (Real.exp ((|x| - |x - δ|) / s))

lemma measurable_rho (s δ : ℝ) : Measurable (rho s δ) := by unfold rho; fun_prop

/-- `Lap(s)` shifted by `δ` has density `ρ` with respect to `Lap(s)`. -/
lemma map_add_eq_withDensity (s δ : ℝ) (hs : 0 < s) :
    (PrivLearn.Generic.laplace s).map (· + δ) =
      (PrivLearn.Generic.laplace s).withDensity (rho s δ) := by
  ext X hX
  rw [Measure.map_apply (measurable_add_const δ) hX, withDensity_apply _ hX, laplace_eq,
    withDensity_apply _ (measurable_add_const δ hX),
    setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_dens s) (measurable_rho s δ) hX,
    ← lintegral_indicator (measurable_add_const δ hX), ← lintegral_indicator hX]
  have hpt : ∀ x, ((· + δ) ⁻¹' X).indicator (dens s) x =
      X.indicator (fun y => dens s (y - δ)) (x + δ) := by
    intro x
    by_cases hx : x + δ ∈ X
    · rw [indicator_of_mem (show x ∈ (· + δ) ⁻¹' X from hx), indicator_of_mem hx]
      simp
    · rw [indicator_of_notMem (show x ∉ (· + δ) ⁻¹' X from hx), indicator_of_notMem hx]
  simp_rw [hpt]
  rw [lintegral_add_right_eq_self (fun y => X.indicator (fun y => dens s (y - δ)) y) δ]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ X
  · rw [indicator_of_mem hy, indicator_of_mem hy]
    simp only [Pi.mul_apply, dens, rho]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [div_mul_eq_mul_div, ← Real.exp_add]
    congr 2
    ring
  · rw [indicator_of_notMem hy, indicator_of_notMem hy]

/-- The `n`-fold product shifted by `δ` in every coordinate has density `∏ ρ(η_i)`. -/
lemma pi_map_shift (s δ : ℝ) (hs : 0 < s) (n : ℕ) :
    (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace s).map
        (fun η : Fin n → ℝ => fun i => η i + δ) =
      (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace s).withDensity
        (fun η => ∏ i, rho s δ (η i)) := by
  have hprob := LSAux.laplace_isProb' s hs
  have hprob' : IsProbabilityMeasure ((PrivLearn.Generic.laplace s).map (· + δ)) :=
    Measure.isProbabilityMeasure_map (measurable_add_const δ).aemeasurable
  have hT : Measurable fun η : Fin n → ℝ => fun i => η i + δ := by fun_prop
  have h1 : Measure.pi (fun _ : Fin n => (PrivLearn.Generic.laplace s).map (· + δ)) =
      (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace s).map
        (fun η : Fin n → ℝ => fun i => η i + δ) := by
    refine Measure.pi_eq fun S hS => ?_
    rw [Measure.map_apply hT (MeasurableSet.univ_pi hS)]
    have : (fun η : Fin n → ℝ => fun i => η i + δ) ⁻¹' univ.pi S =
        univ.pi fun i => (· + δ) ⁻¹' S i := by
      ext η; simp
    rw [this, Measure.pi_pi]
    exact Finset.prod_congr rfl fun i _ => (Measure.map_apply (measurable_add_const δ) (hS i)).symm
  have h2 : Measure.pi (fun _ : Fin n => (PrivLearn.Generic.laplace s).map (· + δ)) =
      (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace s).withDensity
        (fun η => ∏ i, rho s δ (η i)) := by
    refine Measure.pi_eq fun S hS => ?_
    rw [withDensity_apply _ (MeasurableSet.univ_pi hS), ← lintegral_indicator (MeasurableSet.univ_pi hS)]
    have hpt : ∀ η : Fin n → ℝ, (univ.pi S).indicator (fun η => ∏ i, rho s δ (η i)) η =
        ∏ i, (S i).indicator (rho s δ) (η i) := by
      intro η
      by_cases hη : η ∈ univ.pi S
      · rw [indicator_of_mem hη]
        exact Finset.prod_congr rfl fun i _ => (indicator_of_mem (hη i (mem_univ i)) _).symm
      · rw [indicator_of_notMem hη]
        simp only [mem_univ_pi, not_forall] at hη
        obtain ⟨i, hi⟩ := hη
        exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)).symm
    simp_rw [hpt]
    rw [lintegral_pi_prod' _ n _ fun i => (measurable_rho s δ).indicator (hS i)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_add_eq_withDensity s δ hs, withDensity_apply _ (hS i), lintegral_indicator (hS i)]
  rw [← h1, h2]

/-- The shift inequality: `Lapⁿ(B)² ≤ Lapⁿ(B − δ·1) · M(δ)ⁿ`. -/
lemma shift_sq (s δ : ℝ) (hs : 0 < s) (n : ℕ) (B : Set (Fin n → ℝ)) (hB : MeasurableSet B) :
    (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace s) B ^ 2 ≤
      (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace s)
          {η | (fun i => η i + δ) ∈ B} * ENNReal.ofReal (Mb (|δ| / s)) ^ n := by
  have hprob := LSAux.laplace_isProb' s hs
  set L := PrivLearn.Generic.laplace s with hL
  set μ := Measure.pi fun _ : Fin n => L with hμ
  set a : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp ((|x| - |x - δ|) / (2 * s))) with ha
  set a' : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp ((|x - δ| - |x|) / (2 * s)))
    with ha'
  have ham : Measurable a := by rw [ha]; fun_prop
  have ham' : Measurable a' := by rw [ha']; fun_prop
  set f : (Fin n → ℝ) → ENNReal := B.indicator (fun η => ∏ i, a (η i)) with hf
  set g : (Fin n → ℝ) → ENNReal := B.indicator (fun η => ∏ i, a' (η i)) with hg
  have hfm : Measurable f :=
    (Finset.measurable_prod _ fun i _ => ham.comp (measurable_pi_apply i)).indicator hB
  have hgm : Measurable g :=
    (Finset.measurable_prod _ fun i _ => ham'.comp (measurable_pi_apply i)).indicator hB
  have haa : ∀ x, a x * a' x = 1 := by
    intro x
    rw [ha, ha', ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    rw [show (|x| - |x - δ|) / (2 * s) + (|x - δ| - |x|) / (2 * s) = 0 by ring]
    simp
  have hfg : ∀ η, (f * g) η = B.indicator 1 η := by
    intro η
    by_cases hη : η ∈ B
    · simp only [Pi.mul_apply, hf, hg, indicator_of_mem hη, Pi.one_apply]
      rw [← Finset.prod_mul_distrib]
      simp [haa]
    · simp [hf, hg, hη]
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    hfm.aemeasurable hgm.aemeasurable
  have h1 : ∫⁻ η, (f * g) η ∂μ = μ B := by
    simp_rw [hfg]
    rw [lintegral_indicator_one hB]
  have hsq : ∀ x, a x ^ (2 : ℝ) = rho s δ x := by
    intro x
    rw [ENNReal.rpow_two, ha, rho, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 2
    field_simp
    ring
  have hsq' : ∀ x, a' x ^ (2 : ℝ) =
      ENNReal.ofReal (Real.exp ((|x - δ| - |x|) / s)) := by
    intro x
    rw [ENNReal.rpow_two, ha', ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 2
    field_simp
    ring
  have h2 : ∫⁻ η, f η ^ (2 : ℝ) ∂μ = μ {η | (fun i => η i + δ) ∈ B} := by
    have hpt : ∀ η, f η ^ (2 : ℝ) = B.indicator (fun η => ∏ i, rho s δ (η i)) η := by
      intro η
      by_cases hη : η ∈ B
      · rw [hf, indicator_of_mem hη, indicator_of_mem hη, ENNReal.rpow_two, ← Finset.prod_pow]
        exact Finset.prod_congr rfl fun i _ => by rw [← ENNReal.rpow_two, hsq]
      · rw [hf, indicator_of_notMem hη, indicator_of_notMem hη]
        exact ENNReal.zero_rpow_of_pos (by norm_num)
    have hT : Measurable fun η : Fin n → ℝ => fun i => η i + δ := by fun_prop
    simp_rw [hpt]
    rw [lintegral_indicator hB, ← withDensity_apply _ hB, ← pi_map_shift s δ hs n,
      Measure.map_apply hT hB]
    rfl
  have h3 : ∫⁻ η, g η ^ (2 : ℝ) ∂μ ≤ ENNReal.ofReal (Mb (|δ| / s)) ^ n := by
    have hpt : ∀ η, g η ^ (2 : ℝ) ≤
        ∏ i, ENNReal.ofReal (Real.exp ((|η i - δ| - |η i|) / s)) := by
      intro η
      by_cases hη : η ∈ B
      · rw [hg, indicator_of_mem hη, ENNReal.rpow_two, ← Finset.prod_pow]
        exact le_of_eq (Finset.prod_congr rfl fun i _ => by rw [← ENNReal.rpow_two, hsq'])
      · rw [hg, indicator_of_notMem hη, ENNReal.zero_rpow_of_pos (by norm_num)]
        exact bot_le
    calc _ ≤ ∫⁻ η, ∏ i, ENNReal.ofReal (Real.exp ((|η i - δ| - |η i|) / s)) ∂μ :=
          lintegral_mono hpt
      _ = ∏ _i : Fin n, ∫⁻ x, ENNReal.ofReal (Real.exp ((|x - δ| - |x|) / s)) ∂L :=
          lintegral_pi_prod' L n (fun _ x => ENNReal.ofReal (Real.exp ((|x - δ| - |x|) / s)))
            (fun _ => by fun_prop)
      _ ≤ ∏ _i : Fin n, ENNReal.ofReal (Mb (|δ| / s)) :=
          Finset.prod_le_prod' fun i _ => M_le s δ hs
      _ = _ := by simp
  rw [h1] at hholder
  calc μ B ^ 2 ≤ ((∫⁻ η, f η ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫⁻ η, g η ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) ^ 2 := by gcongr
    _ = (∫⁻ η, f η ^ (2 : ℝ) ∂μ) * ∫⁻ η, g η ^ (2 : ℝ) ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num
    _ ≤ _ := by rw [h2]; gcongr

end L56
namespace L56

open MeasureTheory Set

/-- The window radius `R = 32 s / √n`. -/
noncomputable def Rw (s : ℝ) (n : ℕ) : ℝ := 32 * s / Real.sqrt n

lemma exp_neg_four_le : Real.exp (-4) ≤ 1 / 25 := by
  have h2 : (5 : ℝ) ≤ Real.exp 2 := by
    have := Real.quadratic_le_exp_of_nonneg (x := 2) (by norm_num)
    norm_num at this ⊢; linarith
  have h4 : Real.exp 4 = Real.exp 2 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
  have : (25 : ℝ) ≤ Real.exp 4 := by rw [h4]; nlinarith
  rw [Real.exp_neg, inv_eq_one_div]
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) this

/-- Concentration of the noise average at the scale `R/2`. -/
lemma noise_conc (s : ℝ) (hs : 0 < s) (n : ℕ) (hn : 1 ≤ n) :
    (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace s)
        {η | Rw s n / 2 < |(1 / (n : ℝ)) * ∑ i, η i|} ≤ ENNReal.ofReal (1 / 8) := by
  set r := Real.sqrt n with hr
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hr1 : 1 ≤ r := by rw [hr, Real.one_le_sqrt]; exact_mod_cast hn
  have hrr : r * r = n := Real.mul_self_sqrt hnpos.le
  have key : ∀ t : ℝ, 0 < t → |t| ≤ 1 / (2 * s) →
      (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace s)
        {η | Rw s n / 2 < |(1 / (n : ℝ)) * ∑ i, η i|} ≤
        2 * ENNReal.ofReal (Real.exp ((n : ℝ) * (2 * s ^ 2 * t ^ 2) - t * n * (Rw s n / 2))) := by
    intro t ht htb
    have hsub : {η : Fin n → ℝ | Rw s n / 2 < |(1 / (n : ℝ)) * ∑ i, η i|} ⊆
        {η | t * n * (Rw s n / 2) ≤ t * ∑ i, η i} ∪
          {η | t * n * (Rw s n / 2) ≤ (-t) * ∑ i, η i} := by
      intro η hη
      simp only [mem_ofPred_eq] at hη
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / n), one_div, inv_mul_eq_div,
        lt_div_iff₀ hnpos] at hη
      rcases le_abs'.1 hη.le with h | h
      · right; simp only [mem_ofPred_eq]; nlinarith
      · left; simp only [mem_ofPred_eq]; nlinarith
    have hnt : |-t| ≤ 1 / (2 * s) := by rwa [abs_neg]
    calc _ ≤ _ := measure_mono hsub
      _ ≤ _ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * (2 * s ^ 2 * t ^ 2) - t * n * (Rw s n / 2))) +
          ENNReal.ofReal (Real.exp ((n : ℝ) * (2 * s ^ 2 * t ^ 2) - t * n * (Rw s n / 2))) := by
        gcongr
        · exact laplace_sum_tail s t _ hs htb n
        · have := laplace_sum_tail s (-t) (t * n * (Rw s n / 2)) hs hnt n
          rwa [neg_sq] at this
      _ = _ := (two_mul _).symm
  have hfinal : ∀ E : ℝ, E ≤ -4 → 2 * ENNReal.ofReal (Real.exp E) ≤ ENNReal.ofReal (1 / 8) := by
    intro E hE
    have h1 : Real.exp E ≤ 1 / 25 := (Real.exp_le_exp.2 hE).trans exp_neg_four_le
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  by_cases hr8 : 8 ≤ r
  · have ht : (0 : ℝ) < 4 / (s * r) := by positivity
    have htb : |4 / (s * r)| ≤ 1 / (2 * s) := by
      rw [abs_of_pos ht, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    refine (key _ ht htb).trans (hfinal _ ?_)
    have : (n : ℝ) * (2 * s ^ 2 * (4 / (s * r)) ^ 2) - 4 / (s * r) * n * (Rw s n / 2) = -32 := by
      rw [Rw, ← hr, ← hrr]
      field_simp
      ring
    linarith
  · have ht : (0 : ℝ) < 1 / (2 * s) := by positivity
    have htb : |1 / (2 * s)| ≤ 1 / (2 * s) := le_of_eq (abs_of_pos ht)
    refine (key _ ht htb).trans (hfinal _ ?_)
    have : (n : ℝ) * (2 * s ^ 2 * (1 / (2 * s)) ^ 2) - 1 / (2 * s) * n * (Rw s n / 2) =
        r * (r / 2 - 8) := by
      rw [Rw, ← hr, ← hrr]
      field_simp
      ring
    rw [this]
    push Not at hr8
    nlinarith

/-- The constant of the anti-concentration bound. -/
noncomputable def κ0 : ℝ := 49 / (1638400 * Real.exp 49152)

lemma κ0_pos : 0 < κ0 := by unfold κ0; positivity

/-- The cost of shifting by at most `4R` in every coordinate. -/
lemma Mb_pow_le (s : ℝ) (hs : 0 < s) (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ : |δ| ≤ 4 * Rw s n) :
    Mb (|δ| / s) ^ n ≤ Real.exp 49152 := by
  set r := Real.sqrt n with hr
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hr1 : 1 ≤ r := by rw [hr, Real.one_le_sqrt]; exact_mod_cast hn
  have hrr : r * r = n := Real.mul_self_sqrt hnpos.le
  set u := |δ| / s with hu
  have hu0 : 0 ≤ u := by positivity
  have hub : u ≤ 128 / r := by
    rw [hu, div_le_div_iff₀ hs (by positivity)]
    have : 4 * Rw s n * r = 128 * s := by
      rw [Rw, ← hr]; field_simp; ring
    nlinarith
  have hMb0 : 0 ≤ Mb u := by
    unfold Mb
    have := Real.add_one_le_exp u
    have := (Real.exp_pos (-2 * u)).le
    linarith
  by_cases hr256 : 256 ≤ r
  · have hu2 : u ≤ 1 / 2 := by
      refine hub.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    calc Mb u ^ n ≤ (Real.exp (3 * u ^ 2)) ^ n := by
          gcongr
          exact (Mb_le_quad u hu0 hu2).trans (by linarith [Real.add_one_le_exp (3 * u ^ 2)])
      _ = Real.exp (n * (3 * u ^ 2)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp 49152 := by
          apply Real.exp_le_exp.2
          have hur : u * r ≤ 128 := by
            have := mul_le_mul_of_nonneg_right hub (by positivity : (0 : ℝ) ≤ r)
            rwa [div_mul_cancel₀ _ (by positivity)] at this
          rw [← hrr]
          nlinarith [mul_nonneg hu0 (by positivity : (0 : ℝ) ≤ r)]
  · push Not at hr256
    calc Mb u ^ n ≤ (Real.exp u) ^ n := by gcongr; exact Mb_le_exp u hu0
      _ = Real.exp (n * u) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp 49152 := by
          apply Real.exp_le_exp.2
          have hur : u * r ≤ 128 := by
            have := mul_le_mul_of_nonneg_right hub (by positivity : (0 : ℝ) ≤ r)
            rwa [div_mul_cancel₀ _ (by positivity)] at this
          rw [← hrr]
          nlinarith [mul_nonneg hu0 (by positivity : (0 : ℝ) ≤ r)]

/-- Anti-concentration of `d + avg(η)` at scale `τ`, for an offset `|d| ≤ R/2`. -/
lemma core (s τ d : ℝ) (hs : 0 < s) (hτ : 0 < τ) (n : ℕ) (hn : 1 ≤ n)
    (hd : |d| ≤ Rw s n / 2) :
    ENNReal.ofReal (min (7 / 8) (κ0 * τ ^ 2 * n / s ^ 2)) ≤
      (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace s)
        {η | |d + (1 / (n : ℝ)) * ∑ i, η i| ≤ τ} := by
  have hprob := LSAux.laplace_isProb' s hs
  set μ := Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace s with hμ
  set R := Rw s n with hR
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hRpos : 0 < R := by rw [hR, Rw]; positivity
  set N : (Fin n → ℝ) → ℝ := fun η => (1 / (n : ℝ)) * ∑ i, η i with hN
  have hNm : Measurable N := by rw [hN]; fun_prop
  set G := {η : Fin n → ℝ | |N η| ≤ R / 2} with hG
  have hGm : MeasurableSet G := measurableSet_le hNm.abs measurable_const
  have hGc : Gᶜ = {η | R / 2 < |N η|} := by ext; simp [hG, not_le]
  have hGmass : ENNReal.ofReal (7 / 8) ≤ μ G := by
    have h1 : μ Gᶜ ≤ ENNReal.ofReal (1 / 8) := by rw [hGc]; exact noise_conc s hs n hn
    have h2 := prob_compl_eq_one_sub (μ := μ) hGm.compl
    rw [compl_compl] at h2
    rw [h2]
    calc ENNReal.ofReal (7 / 8) = 1 - ENNReal.ofReal (1 / 8) := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]; norm_num
      _ ≤ 1 - μ Gᶜ := tsub_le_tsub_left h1 _
  set S := {η : Fin n → ℝ | |d + N η| ≤ τ} with hS
  have hSm : MeasurableSet S := measurableSet_le (measurable_const.add hNm).abs measurable_const
  show _ ≤ μ S
  by_cases hτR : R ≤ τ
  · have hGS : G ⊆ S := by
      intro η hη
      simp only [hG, hS, mem_ofPred_eq] at hη ⊢
      calc |d + N η| ≤ |d| + |N η| := abs_add_le _ _
        _ ≤ R := by linarith
        _ ≤ τ := hτR
    exact (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans (hGmass.trans (measure_mono hGS))
  push Not at hτR
  set J : ℕ := ⌈R / τ⌉₊ with hJ
  have hJR : R / τ ≤ J := Nat.le_ceil _
  have hJlt : (J : ℝ) < R / τ + 1 := Nat.ceil_lt_add_one (by positivity)
  set I : Finset ℤ := Finset.Icc (-(J : ℤ)) J with hI
  set B : ℤ → Set (Fin n → ℝ) := fun j => {η | |d + N η - 2 * j * τ| ≤ τ} with hB
  have hBm : ∀ j, MeasurableSet (B j) := fun j =>
    measurableSet_le ((measurable_const.add hNm).sub measurable_const).abs measurable_const
  -- cover
  have hcover : G ⊆ ⋃ j ∈ I, B j := by
    intro η hη
    simp only [hG, mem_ofPred_eq] at hη
    set y := d + N η with hy
    have hyR : |y| ≤ R := by
      calc |y| ≤ |d| + |N η| := abs_add_le _ _
        _ ≤ R := by linarith
    set j : ℤ := ⌊(y + τ) / (2 * τ)⌋ with hj
    have h1 : (j : ℝ) ≤ (y + τ) / (2 * τ) := Int.floor_le _
    have h2 : (y + τ) / (2 * τ) < j + 1 := Int.lt_floor_add_one _
    rw [le_div_iff₀ (by positivity)] at h1
    rw [div_lt_iff₀ (by positivity)] at h2
    simp only [mem_iUnion]
    refine ⟨j, ?_, ?_⟩
    · rw [hI, Finset.mem_Icc]
      have hyR' := abs_le.1 hyR
      have hRJ : R ≤ (J : ℝ) * τ := by rwa [div_le_iff₀ hτ] at hJR
      have hJ1 : (1 : ℝ) ≤ J := by
        have : 1 < R / τ := by rw [one_lt_div hτ]; exact hτR
        linarith
      constructor
      · have h3 : 0 < ((j : ℝ) + J + 1) * (2 * τ) := by nlinarith
        have h4 : 0 < (j : ℝ) + J + 1 := (mul_pos_iff_of_pos_right (by positivity)).1 h3
        have : (-(J : ℤ)) - 1 < j := by
          have : (-(J : ℝ)) - 1 < j := by linarith
          exact_mod_cast this
        omega
      · have h3 : ((j : ℝ) - J) * (2 * τ) ≤ 0 := by nlinarith
        have h4 : (j : ℝ) - J ≤ 0 := by
          by_contra hc
          push Not at hc
          have := mul_pos hc (by positivity : (0 : ℝ) < 2 * τ)
          linarith
        have : (j : ℝ) ≤ J := by linarith
        exact_mod_cast this
    · simp only [hB, mem_ofPred_eq]
      rw [abs_le]
      constructor <;> nlinarith
  have hcard : (I.card : ℝ) = 2 * J + 1 := by
    rw [hI, Int.card_Icc]
    have : (J : ℤ) + 1 - -(J : ℤ) = ((2 * J + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
    push_cast; ring
  have hcardpos : (0 : ℝ) < I.card := by rw [hcard]; positivity
  -- pigeonhole
  have hsum : ∑ _j ∈ I, ENNReal.ofReal (7 / 8 / I.card) ≤ ∑ j ∈ I, μ (B j) := by
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity)]
    rw [mul_div_cancel₀ _ hcardpos.ne']
    exact hGmass.trans ((measure_mono hcover).trans (measure_biUnion_finset_le _ _))
  have hIne : I.Nonempty := ⟨0, by rw [hI, Finset.mem_Icc]; omega⟩
  obtain ⟨j, hjI, hjB⟩ := ENNReal.exists_le_of_sum_le hIne hsum
  -- shift block `j` onto the target
  have hshift := shift_sq s (2 * j * τ) hs n (B j) (hBm j)
  have hpre : {η : Fin n → ℝ | (fun i => η i + 2 * j * τ) ∈ B j} = S := by
    ext η
    simp only [hB, hS, mem_ofPred_eq, hN]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_add, ← mul_assoc, one_div_mul_cancel hnpos.ne', one_mul]
    ring_nf
  rw [hpre] at hshift
  have hjb : |(2 * (j : ℝ) * τ)| ≤ 4 * R := by
    rw [hI, Finset.mem_Icc] at hjI
    have hj1 : |(j : ℝ)| ≤ J := by
      rw [abs_le]; constructor <;> [exact_mod_cast hjI.1; exact_mod_cast hjI.2]
    rw [abs_mul, abs_mul, abs_of_pos hτ, abs_two]
    have : (J : ℝ) * τ ≤ R + τ := by
      have := mul_lt_mul_of_pos_right hJlt hτ
      rw [add_mul, div_mul_cancel₀ _ hτ.ne', one_mul] at this
      linarith
    nlinarith [abs_nonneg (j : ℝ)]
  have hM := Mb_pow_le s hs n hn _ hjb
  -- assemble
  have hM0 : 0 ≤ Mb (|2 * (j : ℝ) * τ| / s) := by
    unfold Mb
    have := Real.add_one_le_exp (|2 * (j : ℝ) * τ| / s)
    have := (Real.exp_pos (-2 * (|2 * (j : ℝ) * τ| / s))).le
    have : 0 ≤ |2 * (j : ℝ) * τ| / s := by positivity
    linarith
  have hfin : μ S ≠ ⊤ := measure_ne_top _ _
  have hA : ENNReal.ofReal ((7 / 8 / I.card) ^ 2) ≤
      ENNReal.ofReal ((μ S).toReal * Real.exp 49152) := by
    calc ENNReal.ofReal ((7 / 8 / I.card) ^ 2) = ENNReal.ofReal (7 / 8 / I.card) ^ 2 := by
          rw [ENNReal.ofReal_pow (by positivity)]
      _ ≤ μ (B j) ^ 2 := by gcongr
      _ ≤ μ S * ENNReal.ofReal (Mb (|2 * (j : ℝ) * τ| / s)) ^ n := hshift
      _ = ENNReal.ofReal ((μ S).toReal * Mb (|2 * (j : ℝ) * τ| / s) ^ n) := by
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin,
            ENNReal.ofReal_pow hM0]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hM ENNReal.toReal_nonneg)
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hA
  rw [← ENNReal.ofReal_toReal hfin]
  apply ENNReal.ofReal_le_ofReal
  refine (min_le_right _ _).trans ?_
  -- `κ0 τ² n / s² ≤ (7/(8 card))² / e^{49152} ≤ μ(S)`
  have hcard5 : (I.card : ℝ) ≤ 5 * R / τ := by
    rw [hcard, le_div_iff₀ hτ]
    have : (J : ℝ) * τ ≤ R + τ := by
      have := mul_lt_mul_of_pos_right hJlt hτ
      rw [add_mul, div_mul_cancel₀ _ hτ.ne', one_mul] at this
      linarith
    nlinarith
  have hR2 : R ^ 2 * n = 1024 * s ^ 2 := by
    rw [hR, Rw, div_pow, Real.sq_sqrt hnpos.le]
    field_simp
    ring
  have hE : 0 < Real.exp 49152 := Real.exp_pos _
  have h1 : (7 / 8 / I.card) ^ 2 ≥ (7 * τ / (40 * R)) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    rw [le_div_iff₀ hτ] at hcard5
    nlinarith
  have h2 : (μ S).toReal ≥ (7 * τ / (40 * R)) ^ 2 / Real.exp 49152 := by
    rw [ge_iff_le, div_le_iff₀ hE]
    linarith
  calc κ0 * τ ^ 2 * n / s ^ 2 = (7 * τ / (40 * R)) ^ 2 / Real.exp 49152 := by
        rw [κ0]
        have hs2 : s ^ 2 = R ^ 2 * n / 1024 := by rw [hR2]; ring
        rw [hs2]
        field_simp
        ring
    _ ≤ _ := h2

end L56
namespace L56

open MeasureTheory Set PrivLearn.LocalSim

lemma measurableSet_success {Dom : Type} [MeasurableSpace Dom] (P : Measure Dom) (g : Dom → ℝ)
    (hg : Measurable g) (τ : ℝ) (n : ℕ) :
    MeasurableSet {p : (Fin n → Dom) × (Fin n → ℝ) | |avgResp g p.1 p.2 - ∫ x, g x ∂P| ≤ τ} := by
  refine measurableSet_le ?_ measurable_const
  refine ((Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _).sub
    measurable_const).abs
  exact (hg.comp ((measurable_pi_apply i).comp measurable_fst)).add
    ((measurable_pi_apply i).comp measurable_snd)

lemma avgResp_split {Dom : Type} (g : Dom → ℝ) (n : ℕ) (z : Fin n → Dom) (η : Fin n → ℝ) :
    avgResp g z η = (1 / (n : ℝ)) * ∑ i, g (z i) + (1 / (n : ℝ)) * ∑ i, η i := by
  rw [avgResp, Finset.sum_add_distrib, mul_add]

/-- Anti-concentration of the output of `A_g(n, ε, LR_z)` around the true mean. -/
lemma ac {Dom : Type} [MeasurableSpace Dom] (P : Measure Dom) [IsProbabilityMeasure P]
    (g : Dom → ℝ) (b ε τ : ℝ) (n : ℕ) (hg : Measurable g) (hgb : ∀ u, |g u| ≤ b) (hb : 0 < b)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 < τ) (hn : 1 ≤ n) :
    ENNReal.ofReal (7 / 8 * min (7 / 8) (κ0 * τ ^ 2 * n / (2 * b / ε) ^ 2)) ≤
      ((Measure.pi fun _ : Fin n => P).prod
          (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace (2 * b / ε)))
        {p | |avgResp g p.1 p.2 - ∫ x, g x ∂P| ≤ τ} := by
  set s := 2 * b / ε with hsdef
  have hs : 0 < s := by positivity
  have hprob := LSAux.laplace_isProb' s hs
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set v := ∫ x, g x ∂P with hv
  set R := Rw s n with hR
  have hRpos : 0 < R := by rw [hR, Rw]; positivity
  rw [Measure.prod_apply (measurableSet_success P g hg τ n)]
  set D : (Fin n → Dom) → ℝ := fun z => (1 / (n : ℝ)) * ∑ i, g (z i) - v with hD
  have hDm : Measurable D := by
    rw [hD]
    exact (Measurable.const_mul (Finset.measurable_sum _ fun i _ =>
      hg.comp (measurable_pi_apply i)) _).sub measurable_const
  set Good := {z : Fin n → Dom | |D z| < R / 2} with hGood
  have hGm : MeasurableSet Good := measurableSet_lt hDm.abs measurable_const
  have hGood_mass : ENNReal.ofReal (7 / 8) ≤ (Measure.pi fun _ : Fin n => P) Good := by
    have hH := PrivLearn.LocalSim.hoeffding_display P g hg b R hb hRpos hgb n
    have hc : Goodᶜ = {u : Fin n → Dom | R / 2 ≤ |(1 / (n : ℝ)) * ∑ i, g (u i) - v|} := by
      ext z; simp [hGood, hD, not_lt]
    have hsmall : 2 * Real.exp (-(R ^ 2 * n) / (8 * b ^ 2)) ≤ 1 / 8 := by
      have hR2 : R ^ 2 * n = 1024 * s ^ 2 := by
        rw [hR, Rw, div_pow, Real.sq_sqrt hnpos.le]
        field_simp
        ring
      have hexp : -(R ^ 2 * n) / (8 * b ^ 2) ≤ -4 := by
        rw [hR2, hsdef, div_le_iff₀ (by positivity)]
        have hε2 : ε ^ 2 ≤ 1 := by nlinarith
        have : (2 * b / ε) ^ 2 = 4 * b ^ 2 / ε ^ 2 := by ring
        rw [this]
        rw [show -(1024 * (4 * b ^ 2 / ε ^ 2)) = -(4096 * b ^ 2) / ε ^ 2 by ring,
          div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg b]
      have := (Real.exp_le_exp.2 hexp).trans exp_neg_four_le
      linarith
    have h1 : (Measure.pi fun _ : Fin n => P) Goodᶜ ≤ ENNReal.ofReal (1 / 8) := by
      rw [hc]; exact hH.trans (ENNReal.ofReal_le_ofReal hsmall)
    have h2 := prob_compl_eq_one_sub (μ := Measure.pi fun _ : Fin n => P) hGm.compl
    rw [compl_compl] at h2
    rw [h2]
    calc ENNReal.ofReal (7 / 8) = 1 - ENNReal.ofReal (1 / 8) := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]; norm_num
      _ ≤ 1 - (Measure.pi fun _ : Fin n => P) Goodᶜ := tsub_le_tsub_left h1 _
  have hpt : ∀ z, Good.indicator
      (fun _ => ENNReal.ofReal (min (7 / 8) (κ0 * τ ^ 2 * n / s ^ 2))) z ≤
      (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace s)
        (Prod.mk z ⁻¹' {p | |avgResp g p.1 p.2 - ∫ x, g x ∂P| ≤ τ}) := by
    intro z
    by_cases hz : z ∈ Good
    · rw [indicator_of_mem hz]
      have hsec : Prod.mk z ⁻¹' {p : (Fin n → Dom) × (Fin n → ℝ) |
          |avgResp g p.1 p.2 - ∫ x, g x ∂P| ≤ τ} =
          {η | |D z + (1 / (n : ℝ)) * ∑ i, η i| ≤ τ} := by
        ext η
        simp only [mem_preimage, mem_ofPred_eq, avgResp_split, hD, hv]
        ring_nf
      rw [hsec]
      exact core s τ (D z) hs hτ n hn (le_of_lt hz)
    · rw [indicator_of_notMem hz]
      exact bot_le
  calc ENNReal.ofReal (7 / 8 * min (7 / 8) (κ0 * τ ^ 2 * n / s ^ 2))
      = ENNReal.ofReal (min (7 / 8) (κ0 * τ ^ 2 * n / s ^ 2)) * ENNReal.ofReal (7 / 8) := by
        rw [mul_comm (7 / 8 : ℝ), ENNReal.ofReal_mul (le_min (by norm_num)
          (div_nonneg (mul_nonneg (mul_nonneg κ0_pos.le (sq_nonneg τ)) (Nat.cast_nonneg n))
            (sq_nonneg s)))]
    _ ≤ ENNReal.ofReal (min (7 / 8) (κ0 * τ ^ 2 * n / s ^ 2)) *
        (Measure.pi fun _ : Fin n => P) Good := by gcongr
    _ = ∫⁻ z, Good.indicator
        (fun _ => ENNReal.ofReal (min (7 / 8) (κ0 * τ ^ 2 * n / s ^ 2))) z
          ∂(Measure.pi fun _ : Fin n => P) := (lintegral_indicator_const hGm _).symm
    _ ≤ _ := lintegral_mono hpt

end L56

open MeasureTheory Set PrivLearn.LocalSim L56

theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Dom : Type) [MeasurableSpace Dom] (P : Measure Dom) [IsProbabilityMeasure P]
        (g : Dom → ℝ) (b ε τ β : ℝ) (n : ℕ),
        Measurable g → (∀ u, |g u| ≤ b) →
        0 < b → 0 < ε → ε ≤ 1 → 0 < τ → ε * τ ≤ 4 * b → 0 < β → β < 1 →
        c * Real.log (1 / β) * b ^ 2 / (ε ^ 2 * τ ^ 2) ≤ n →
        ENNReal.ofReal (1 - β) ≤
          ((Measure.pi fun _ : Fin n => P).prod
              (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace (2 * b / ε)))
            {p | |avgResp g p.1 p.2 - ∫ x, g x ∂P| ≤ τ} := by
  obtain ⟨cL, hcL, hLA⟩ := PrivLearn.LocalSim.laplace_average
  have hκ := κ0_pos
  refine ⟨max (max 24 cL) (32 / (7 * κ0)), by positivity, ?_⟩
  intro Dom _ P _ g b ε τ β n hg hgb hb hε hε1 hτ hετ hβ hβ1 hn
  set c := max (max 24 cL) (32 / (7 * κ0)) with hc
  have hlog : 0 < Real.log (1 / β) := Real.log_pos (by rw [one_lt_div hβ]; exact hβ1)
  have hthr : 0 < c * Real.log (1 / β) * b ^ 2 / (ε ^ 2 * τ ^ 2) := by positivity
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le hthr hn
  have hn1 : 1 ≤ n := by exact_mod_cast hnpos
  have hn' : c * Real.log (1 / β) * b ^ 2 ≤ n * (ε ^ 2 * τ ^ 2) := by
    rwa [div_le_iff₀ (by positivity)] at hn
  set s := 2 * b / ε with hsdef
  have hs : 0 < s := by positivity
  have hprob := LSAux.laplace_isProb' s hs
  set ν := (Measure.pi fun _ : Fin n => P).prod
    (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace s) with hν
  set S := {p : (Fin n → Dom) × (Fin n → ℝ) | |avgResp g p.1 p.2 - ∫ x, g x ∂P| ≤ τ} with hS
  have hSm : MeasurableSet S := measurableSet_success P g hg τ n
  by_cases hβ2 : β ≤ 1 / 2
  · -- small `β`: Hoeffding for the data and the Laplace tail bound for the noise
    set v := ∫ x, g x ∂P with hv
    set A1 := {u : Fin n → Dom | τ / 2 ≤ |(1 / (n : ℝ)) * ∑ i, g (u i) - v|} with hA1
    set A2 := {η : Fin n → ℝ | τ / 2 < |(1 / (n : ℝ)) * ∑ i, η i|} with hA2
    have hsub : Sᶜ ⊆ A1 ×ˢ univ ∪ univ ×ˢ A2 := by
      intro p hp
      simp only [hS, mem_compl_iff, mem_ofPred_eq, not_le] at hp
      by_contra hc'
      simp only [mem_union, mem_prod, mem_univ, and_true, true_and, hA1, hA2, mem_ofPred_eq,
        not_or, not_le, not_lt] at hc'
      rw [avgResp_split] at hp
      have := abs_add_le ((1 / (n : ℝ)) * ∑ i, g (p.1 i) - v) ((1 / (n : ℝ)) * ∑ i, p.2 i)
      have e : (1 / (n : ℝ)) * ∑ i, g (p.1 i) + (1 / (n : ℝ)) * ∑ i, p.2 i - v =
          (1 / (n : ℝ)) * ∑ i, g (p.1 i) - v + (1 / (n : ℝ)) * ∑ i, p.2 i := by ring
      rw [e] at hp
      linarith [hc'.1, hc'.2]
    have hH := PrivLearn.LocalSim.hoeffding_display P g hg b τ hb hτ hgb n
    have hL := hLA b ε τ β n hb hε hτ hετ hβ hβ2 (by
      refine le_trans ?_ hn
      gcongr
      exact le_trans (le_max_right _ _) (le_max_left _ _))
    have hsmall : 2 * Real.exp (-(τ ^ 2 * n) / (8 * b ^ 2)) ≤ β / 2 := by
      have hε2 : ε ^ 2 ≤ 1 := by nlinarith
      have h24 : 24 * Real.log (1 / β) * b ^ 2 ≤ n * τ ^ 2 := by
        have : 24 ≤ c := le_trans (le_max_left _ _) (le_max_left _ _)
        have h1 : 24 * Real.log (1 / β) * b ^ 2 ≤ c * Real.log (1 / β) * b ^ 2 := by gcongr
        have h2 : (n : ℝ) * (ε ^ 2 * τ ^ 2) ≤ n * τ ^ 2 := by
          have : ε ^ 2 * τ ^ 2 ≤ τ ^ 2 := by nlinarith [sq_nonneg τ]
          exact mul_le_mul_of_nonneg_left this hnpos.le
        linarith
      have hexp : -(τ ^ 2 * n) / (8 * b ^ 2) ≤ 3 * Real.log β := by
        rw [div_le_iff₀ (by positivity)]
        have : Real.log (1 / β) = -Real.log β := by rw [one_div, Real.log_inv]
        rw [this] at h24
        nlinarith
      have h3 : Real.exp (3 * Real.log β) = β ^ 3 := by
        rw [show (3 : ℝ) * Real.log β = ((3 : ℕ) : ℝ) * Real.log β by norm_num,
          Real.exp_nat_mul, Real.exp_log hβ]
      have := Real.exp_le_exp.2 hexp
      rw [h3] at this
      have hb2 : β ^ 2 ≤ 1 / 4 := by nlinarith
      have hb3 : β ^ 3 ≤ β / 4 := by nlinarith
      linarith
    have hfail : ν Sᶜ ≤ ENNReal.ofReal β := by
      calc ν Sᶜ ≤ ν (A1 ×ˢ univ ∪ univ ×ˢ A2) := measure_mono hsub
        _ ≤ ν (A1 ×ˢ univ) + ν (univ ×ˢ A2) := measure_union_le _ _
        _ = (Measure.pi fun _ : Fin n => P) A1 +
            (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace s) A2 := by
          rw [hν, Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ, mul_one,
            one_mul]
        _ ≤ ENNReal.ofReal (2 * Real.exp (-(τ ^ 2 * n) / (8 * b ^ 2))) + ENNReal.ofReal (β / 2) :=
          add_le_add hH hL
        _ ≤ ENNReal.ofReal (β / 2) + ENNReal.ofReal (β / 2) := by
          gcongr
        _ = ENNReal.ofReal β := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    have h2 := prob_compl_eq_one_sub (μ := ν) hSm.compl
    rw [compl_compl] at h2
    show ENNReal.ofReal (1 - β) ≤ ν S
    rw [h2, ENNReal.ofReal_sub _ hβ.le, ENNReal.ofReal_one]
    exact tsub_le_tsub_left hfail _
  · -- large `β`: anti-concentration
    push Not at hβ2
    have hac := ac P g b ε τ n hg hgb hb hε hε1 hτ hn1
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hac
    have h1β : 1 - β ≤ Real.log (1 / β) := by
      have := Real.log_le_sub_one_of_pos hβ
      rw [one_div, Real.log_inv]
      linarith
    have hlogle : Real.log (1 / β) ≤ n * (ε ^ 2 * τ ^ 2) / (c * b ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hcκ : 32 / (7 * κ0) ≤ c := le_max_right _ _
    have hB : n * (ε ^ 2 * τ ^ 2) / (c * b ^ 2) ≤ 7 / 8 * (κ0 * τ ^ 2 * n / s ^ 2) := by
      rw [hsdef, div_le_iff₀ (by positivity)]
      have hcpos : 0 < c := by positivity
      have : 1 ≤ c * (7 * κ0 / 32) := by
        rw [div_le_iff₀ (by positivity)] at hcκ
        linarith
      field_simp
      nlinarith [mul_pos hnpos (mul_pos (pow_pos hε 2) (pow_pos hτ 2)), sq_nonneg b,
        mul_pos (mul_pos hnpos (pow_pos hτ 2)) (pow_pos hε 2)]
    rw [mul_min_of_nonneg _ _ (by norm_num)]
    apply le_min
    · linarith
    · linarith
