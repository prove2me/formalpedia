-- Prove2me | solution 1 for RGMISFast.eq_28
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-15T23:01:12.13612+00:00
-- url     : https://prove2.me/submissions/3843c0e1-5f47-4b87-a981-029ac14139fb

import Definitions.Def_RGMISFast_gammaA
open MeasureTheory ProbabilityTheory RGMISFast
set_option autoImplicit false

lemma exp_one_ae_nonnegative : ∀ᵐ x ∂(expMeasure 1), 0 ≤ x := by
  rw [ae_iff]
  simp only [not_le]
  change (expMeasure 1) (Set.Iio 0) = 0
  rw [show expMeasure 1 = volume.withDensity (gammaPDF 1 1) from rfl,
    withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

lemma exp_one_integrable_exp {f : ℝ → ℝ} (hf : Measurable f)
    (hneg : ∀ᵐ x ∂(expMeasure 1), f x ≤ 0) :
    Integrable (fun x => Real.exp (f x)) (expMeasure 1) := by
  letI := isProbabilityMeasure_expMeasure (r := (1:ℝ)) (by norm_num)
  apply (integrable_const (1:ℝ)).mono' (hf.exp.aestronglyMeasurable)
  filter_upwards [hneg] with x hx
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using Real.exp_le_one_iff.mpr hx

lemma exp_one_laplace (a : ℝ) (ha : 0 < a) :
    (∫ x, Real.exp (-2*x/a) ∂(expMeasure 1)) = a/(a+2) := by
  change (∫ x, Real.exp (-2*x/a) ∂volume.withDensity (exponentialPDF 1)) = _
  have hmeas : Measurable (exponentialPDF 1) := (measurable_exponentialPDFReal 1).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul
    hmeas
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  have he : (fun x : ℝ => (exponentialPDF 1 x).toReal • Real.exp (-2*x/a)) =
      (Set.Ici (0:ℝ)).indicator (fun x => Real.exp ((-(1+2/a))*x)) := by
    funext x
    by_cases hx : 0 ≤ x
    · simp only [exponentialPDF_eq,if_pos hx,one_mul,ENNReal.toReal_ofReal (Real.exp_pos _).le,
        smul_eq_mul,Set.indicator_of_mem (show x ∈ Set.Ici (0:ℝ) from hx)]
      rw [← Real.exp_add]
      congr 1; ring
    · simp [exponentialPDF_eq,hx,Set.indicator_of_notMem hx]
  rw [he,integral_indicator measurableSet_Ici,integral_Ici_eq_integral_Ioi]
  have hn : -(1+2/a) < 0 := by
    have hp : 0 < 2/a := by positivity
    linarith
  rw [integral_exp_mul_Ioi hn 0]
  simp only [mul_zero,Real.exp_zero]
  have hp : a+2 ≠ 0 := by linarith
  field_simp
  <;> ring

lemma exponential_reciprocal_bound (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.exp (-2/x) ≤ x*Real.exp (-2) := by
  have hi : 1 ≤ x⁻¹ := (one_le_inv₀ hx).mpr hx1
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at hl
  have he : Real.exp (2-2/x) ≤ x := by
    calc
      _ ≤ Real.exp (Real.log x) := by
        apply Real.exp_le_exp.mpr
        simp only [div_eq_mul_inv]
        linarith
      _ = x := Real.exp_log hx
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-2)).le
  rw [← Real.exp_add] at hm
  convert hm using 1 <;> congr 1 <;> ring

lemma gammaA_split_bound (a : ℝ) (ha : 0 < a) :
    gammaA a ≤ Real.exp (-2)*(∫ x,Real.exp (-2*x/a) ∂(expMeasure 1)) + Real.exp (-2*a0/a) := by
  letI := isProbabilityMeasure_expMeasure (r := (1:ℝ)) (by norm_num)
  have ha0 : 0 < a0 := Real.exp_pos 2
  have hi : Integrable (fun x:ℝ => Real.exp (-2*x/a)) (expMeasure 1) := by
    apply exp_one_integrable_exp (by fun_prop)
    filter_upwards [exp_one_ae_nonnegative] with x hx
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) ha.le
  have hg : Integrable (fun x:ℝ => Real.exp (-2*min (a+x) a0/a)) (expMeasure 1) := by
    apply exp_one_integrable_exp (by fun_prop)
    filter_upwards [exp_one_ae_nonnegative] with x hx
    have hmin : 0 ≤ min (a+x) a0 := le_min (by linarith) ha0.le
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) ha.le
  have hb : ∀x:ℝ, Real.exp (-2*min (a+x) a0/a) ≤
      Real.exp (-2)*Real.exp (-2*x/a)+Real.exp (-2*a0/a) := by
    intro x
    by_cases hx : a+x ≤ a0
    · rw [min_eq_left hx,←Real.exp_add]
      have he : -2*(a+x)/a = -2 + -2*x/a := by field_simp; ring
      rw [he]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [min_eq_right (le_of_not_ge hx)]
      exact le_add_of_nonneg_left (by positivity)
  have hmono := integral_mono hg ((hi.const_mul (Real.exp (-2))).add (integrable_const _)) hb
  simp only [Pi.add_apply] at hmono
  rw [integral_add (hi.const_mul _) (integrable_const _),integral_const_mul] at hmono
  simpa [gammaA] using hmono

lemma gammaA_scalar_bound (a : ℝ) (ha : 0 < a) (ha0 : a ≤ a0) :
    a*Real.exp (-2)/(a+2)+Real.exp (-2*a0/a) ≤ a*Real.exp (-2)*(1/2+1/a0) := by
  have hp : 0 < a0 := Real.exp_pos 2
  have hx := exponential_reciprocal_bound (a/a0) (div_pos ha hp) ((div_le_one hp).mpr ha0)
  have he : -2/(a/a0) = -2*a0/a := by field_simp
  rw [he] at hx
  have hfrac := div_le_div_of_nonneg_left (show 0 ≤ a*Real.exp (-2) by positivity)
    (by norm_num : (0:ℝ)<2) (show 2 ≤ a+2 by linarith)
  calc
    _ ≤ a*Real.exp (-2)/2+(a/a0)*Real.exp (-2) := add_le_add hfrac hx
    _ = _ := by ring

lemma gammaA_ratio_bound (a : ℝ) (ha : 0 < a) (ha0 : a ≤ a0) :
    2*Real.exp 1*gammaA a/a ≤ Real.exp (-1)+2*Real.exp (-3) := by
  have hg := gammaA_split_bound a ha
  rw [exp_one_laplace a ha] at hg
  have hb := gammaA_scalar_bound a ha ha0
  have hgamma : gammaA a ≤ a*Real.exp (-2)*(1/2+1/a0) := by
    calc
      _ ≤ _ := hg
      _ = a*Real.exp (-2)/(a+2)+Real.exp (-2*a0/a) := by ring
      _ ≤ _ := hb
  have hh := mul_le_mul_of_nonneg_left hgamma (show 0 ≤ 2*Real.exp 1/a by positivity)
  have he2 : Real.exp 2 = (Real.exp 1)^2 := by rw [←Real.exp_nat_mul]; norm_num
  have he3 : Real.exp 3 = (Real.exp 1)^3 := by rw [←Real.exp_nat_mul]; norm_num
  have he : (2*Real.exp 1/a)*(a*Real.exp (-2)*(1/2+1/a0)) =
      Real.exp (-1)+2*Real.exp (-3) := by
    unfold a0
    simp only [Real.exp_neg,he2,he3]
    have hene : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
    field_simp
    <;> ring
  rw [he] at hh
  calc
    _ = (2*Real.exp 1/a)*gammaA a := by ring
    _ ≤ _ := hh

lemma gammaA_ratio_lt_half : Real.exp (-1)+2*Real.exp (-3) < (1/2:ℝ) := by
  have h := Real.exp_one_gt_d9
  have hp := Real.exp_pos 1
  have hbound : (27/10:ℝ) < Real.exp 1 := by linarith
  have he3 : Real.exp 3 = (Real.exp 1)^3 := by rw [←Real.exp_nat_mul]; norm_num
  simp only [Real.exp_neg,he3]
  have hi : (Real.exp 1)⁻¹ ≤ (10/27:ℝ) := by
    apply (inv_le_comm₀ hp (by norm_num)).mpr
    norm_num
    linarith
  have hi3 : ((Real.exp 1)⁻¹)^3 ≤ (10/27:ℝ)^3 := pow_le_pow_left₀ (by positivity) hi _
  rw [← inv_pow]

  nlinarith

theorem eq28_complete (a : ℝ) (ha : 0 < a) (ha0 : a ≤ a0) :
    gammaA a ≤ Real.exp (-2) * (∫ x, Real.exp (-2*x/a) ∂(expMeasure 1)) + Real.exp (-2*a0/a) ∧
    Real.exp (-2) * (∫ x, Real.exp (-2*x/a) ∂(expMeasure 1)) + Real.exp (-2*a0/a) =
      a*Real.exp (-2)/(a+2)+Real.exp (-2*a0/a) ∧
    a*Real.exp (-2)/(a+2)+Real.exp (-2*a0/a) ≤ a*Real.exp (-2)*(1/2+1/a0) ∧
    (∀x:ℝ,0 < x → x ≤ 1 → Real.exp (-2/x) ≤ x*Real.exp (-2)) ∧
    2*Real.exp 1*gammaA a/a ≤ Real.exp (-1)+2*Real.exp (-3) ∧
    Real.exp (-1)+2*Real.exp (-3)<1/2 := by
  refine ⟨gammaA_split_bound a ha,?_,gammaA_scalar_bound a ha ha0,
    exponential_reciprocal_bound,gammaA_ratio_bound a ha ha0,gammaA_ratio_lt_half⟩
  rw [exp_one_laplace a ha]
  ring

theorem solution (a : ℝ) (ha : 0 < a) (ha0 : a ≤ a0) :
    gammaA a ≤ Real.exp (-2) * (∫ x, Real.exp (-2 * x / a) ∂(expMeasure 1)) +
        Real.exp (-2 * a0 / a) ∧
    Real.exp (-2) * (∫ x, Real.exp (-2 * x / a) ∂(expMeasure 1)) + Real.exp (-2 * a0 / a) =
        a * Real.exp (-2) / (a + 2) + Real.exp (-2 * a0 / a) ∧
    a * Real.exp (-2) / (a + 2) + Real.exp (-2 * a0 / a) ≤ a * Real.exp (-2) * (1 / 2 + 1 / a0) ∧
    (∀ x : ℝ, 0 < x → x ≤ 1 → Real.exp (-2 / x) ≤ x * Real.exp (-2)) ∧
    2 * Real.exp 1 * gammaA a / a ≤ Real.exp (-1) + 2 * Real.exp (-3) ∧
    Real.exp (-1) + 2 * Real.exp (-3) < 1 / 2 := eq28_complete a ha ha0

