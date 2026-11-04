-- Prove2me | solution 1 for RamanujanLostNotebook.PartIV.eq_18_2_23
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-03T22:48:55.267673+00:00
-- url     : https://prove2.me/submissions/d6a52245-3984-4a3c-ab0c-db73504168f9

import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open Real Complex MeasureTheory FourierTransform

namespace SechFT

lemma sech_integrable_real : Integrable (fun x : ℝ => (Real.cosh (π * x))⁻¹) := by
  have hc : Continuous (fun x : ℝ => (Real.cosh (π * x))⁻¹) :=
    (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).inv₀
      (fun x => (Real.cosh_pos _).ne')
  have hb : ∀ y : ℝ, (Real.cosh y)⁻¹ ≤ 2 * Real.exp (-y) := by
    intro y
    rw [inv_eq_one_div, div_le_iff₀ (Real.cosh_pos _), Real.cosh_eq]
    have h : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos y, Real.exp_pos (-y)]
  have hb' : ∀ y : ℝ, (Real.cosh y)⁻¹ ≤ 2 * Real.exp y := by
    intro y
    simpa using hb (-y)
  have h1 : IntegrableOn (fun x : ℝ => (Real.cosh (π * x))⁻¹) (Set.Iic 0) := by
    refine Integrable.mono' ((integrableOn_exp_mul_Iic Real.pi_pos 0).const_mul 2)
      hc.aestronglyMeasurable.restrict ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (inv_nonneg.2 (Real.cosh_pos _).le)]
    exact hb' _
  have h2 : IntegrableOn (fun x : ℝ => (Real.cosh (π * x))⁻¹) (Set.Ioi 0) := by
    refine Integrable.mono'
      ((integrableOn_exp_mul_Ioi (a := -π) (by linarith [Real.pi_pos]) 0).const_mul 2)
      hc.aestronglyMeasurable.restrict ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (inv_nonneg.2 (Real.cosh_pos _).le)]
    have := hb (π * x)
    convert this using 2
    ring_nf
  have := h1.union h2
  rwa [Set.Iic_union_Ioi, integrableOn_univ] at this

theorem sech_integrable :
    Integrable (fun x : ℝ => (((Real.cosh (π * x))⁻¹ : ℝ) : ℂ)) :=
  sech_integrable_real.ofReal

/-- logistic function of `2πx` -/
noncomputable def lg (x : ℝ) : ℝ := Real.exp (2 * π * x) / (1 + Real.exp (2 * π * x))

lemma hasDerivAt_lg (x : ℝ) : HasDerivAt lg (2 * π * (lg x * (1 - lg x))) x := by
  have h1 : HasDerivAt (fun x : ℝ => Real.exp (2 * π * x)) (Real.exp (2 * π * x) * (2 * π)) x := by
    simpa using ((hasDerivAt_id x).const_mul (2 * π)).exp
  have h2 := h1.div (h1.const_add 1) (by positivity)
  refine HasDerivAt.congr_deriv h2 ?_
  unfold lg
  field_simp

lemma lg_injective : Function.Injective lg := by
  intro x y h
  unfold lg at h
  have h1 : (0:ℝ) < 1 + Real.exp (2 * π * x) := by positivity
  have h2 : (0:ℝ) < 1 + Real.exp (2 * π * y) := by positivity
  rw [div_eq_div_iff h1.ne' h2.ne'] at h
  have h3 : Real.exp (2 * π * x) = Real.exp (2 * π * y) := by linarith
  have h4 := Real.exp_injective h3
  have := Real.pi_pos
  nlinarith

lemma image_lg : lg '' Set.univ = Set.Ioo 0 1 := by
  ext y
  constructor
  · rintro ⟨x, -, rfl⟩
    unfold lg
    constructor
    · positivity
    · rw [div_lt_one (by positivity)]; linarith
  · rintro ⟨h0, h1⟩
    refine ⟨Real.log (y / (1 - y)) / (2 * π), trivial, ?_⟩
    have hy : 0 < y / (1 - y) := div_pos h0 (by linarith)
    have : 2 * π * (Real.log (y / (1 - y)) / (2 * π)) = Real.log (y / (1 - y)) := by
      have := Real.pi_pos
      field_simp
    unfold lg
    rw [this, Real.exp_log hy]
    have : 1 - y ≠ 0 := by linarith
    field_simp
    ring

lemma pointwise (x t : ℝ) :
    |2 * π * (lg x * (1 - lg x))| •
      (((lg x : ℝ) : ℂ) ^ ((1 / 2 - t * I) - 1) * (1 - ((lg x : ℝ) : ℂ)) ^ ((1 / 2 + t * I) - 1)) =
    (π : ℂ) * (cexp (↑(-2 * π * x * t) * I) • (((Real.cosh (π * x))⁻¹ : ℝ) : ℂ)) := by
  set E := Real.exp (2 * π * x) with hE
  set w := Real.exp (π * x) with hw
  have hw0 : 0 < w := Real.exp_pos _
  have hE0 : 0 < E := Real.exp_pos _
  have hEw : E = w ^ 2 := by rw [hE, hw, sq, ← Real.exp_add]; ring_nf
  have hlg : lg x = E / (1 + E) := rfl
  have h1lg : 1 - lg x = (1 + E)⁻¹ := by rw [hlg]; field_simp; ring
  have hpos1 : 0 < lg x := by rw [hlg]; positivity
  have hpos2 : 0 < 1 - lg x := by rw [h1lg]; positivity
  set L := Real.log (1 + E) with hL
  have hlog1 : Real.log (lg x) = 2 * π * x - L := by
    rw [hlg, Real.log_div hE0.ne' (by positivity), hE, Real.log_exp]
  have hlog2 : Real.log (1 - lg x) = -L := by
    rw [h1lg, Real.log_inv]
  have e1 : ((lg x : ℝ) : ℂ) ^ ((1 / 2 - t * I) - 1)
      = cexp (↑(2 * π * x - L) * ((1 / 2 - t * I) - 1)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos1.ne'),
      ← Complex.ofReal_log hpos1.le, hlog1]
  have e2 : (1 - ((lg x : ℝ) : ℂ)) ^ ((1 / 2 + t * I) - 1)
      = cexp (↑(-L) * ((1 / 2 + t * I) - 1)) := by
    have : (1 - ((lg x : ℝ) : ℂ)) = ((1 - lg x : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos2.ne'),
      ← Complex.ofReal_log hpos2.le, hlog2]
  have hprod : ((lg x : ℝ) : ℂ) ^ ((1 / 2 - t * I) - 1) *
      (1 - ((lg x : ℝ) : ℂ)) ^ ((1 / 2 + t * I) - 1)
      = ((Real.exp (L - π * x) : ℝ) : ℂ) * cexp (↑(-2 * π * x * t) * I) := by
    rw [e1, e2, ← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hreal : |2 * π * (lg x * (1 - lg x))| * Real.exp (L - π * x)
      = π * (Real.cosh (π * x))⁻¹ := by
    have hnn : 0 ≤ 2 * π * (lg x * (1 - lg x)) := by
      have := Real.pi_pos
      positivity
    rw [abs_of_nonneg hnn, Real.exp_sub, hL, Real.exp_log (by positivity), Real.cosh_eq,
      Real.exp_neg, h1lg, hlg, ← hw, hEw]
    field_simp
    ring
  rw [Complex.real_smul, hprod, smul_eq_mul]
  calc ((|2 * π * (lg x * (1 - lg x))| : ℝ) : ℂ) *
        (((Real.exp (L - π * x) : ℝ) : ℂ) * cexp (↑(-2 * π * x * t) * I))
      = ((|2 * π * (lg x * (1 - lg x))| * Real.exp (L - π * x) : ℝ) : ℂ) *
          cexp (↑(-2 * π * x * t) * I) := by push_cast; ring
    _ = _ := by rw [hreal]; push_cast; ring

lemma beta_eq (t : ℝ) :
    Complex.betaIntegral (1 / 2 - t * I) (1 / 2 + t * I)
      = π * 𝓕 (fun x : ℝ => (((Real.cosh (π * x))⁻¹ : ℝ) : ℂ)) t := by
  rw [fourier_real_eq_integral_exp_smul]
  unfold Complex.betaIntegral
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, ← image_lg,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (hasDerivAt_lg x).hasDerivWithinAt) lg_injective.injOn,
    Measure.restrict_univ, ← integral_const_mul]
  congr 1
  ext x
  exact pointwise x t

theorem fourier_sech :
    𝓕 (fun x : ℝ => (((Real.cosh (π * x))⁻¹ : ℝ) : ℂ))
      = fun t : ℝ => (((Real.cosh (π * t))⁻¹ : ℝ) : ℂ) := by
  funext t
  have hb := beta_eq t
  set u : ℂ := 1 / 2 - t * I with hu
  have hre : 0 < u.re := by simp [hu]
  have hre' : 0 < (1 / 2 + (t : ℂ) * I).re := by simp
  have hsum : u + (1 / 2 + (t : ℂ) * I) = 1 := by rw [hu]; ring
  have hv : (1 / 2 + (t : ℂ) * I) = 1 - u := by rw [hu]; ring
  have h1 := Complex.Gamma_mul_Gamma_eq_betaIntegral hre hre'
  rw [hsum, Complex.Gamma_one, one_mul, hv] at h1
  have h2 := Complex.Gamma_mul_Gamma_one_sub u
  rw [h1] at h2
  rw [hv] at hb
  have hsin : Complex.sin (π * u) = ((Real.cosh (π * t) : ℝ) : ℂ) := by
    have : (π : ℂ) * u = (π / 2 : ℂ) - ((π * t : ℝ) : ℂ) * I := by rw [hu]; push_cast; ring
    rw [this, Complex.sin_sub, Complex.sin_pi_div_two, Complex.cos_pi_div_two, Complex.cos_mul_I,
      Complex.ofReal_cosh]
    simp
  rw [hsin] at h2
  have hc : ((Real.cosh (π * t) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.cosh_pos _).ne'
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [h2] at hb
  rw [Complex.ofReal_inv]
  apply mul_left_cancel₀ hpi
  rw [← hb, div_eq_mul_inv]

end SechFT

#print axioms SechFT.sech_integrable
#print axioms SechFT.fourier_sech

namespace GaussSech
open SechFT

/-- The real Gaussian `exp (-(a x)^2)` as a complex-valued function. -/
noncomputable def gauss (a : ℝ) (x : ℝ) : ℂ := ((Real.exp (-(a * x) ^ 2) : ℝ) : ℂ)

lemma gauss_eq (a : ℝ) (ha : 0 < a) :
    gauss a = fun x : ℝ => cexp (-π * (((a ^ 2 / π : ℝ)) : ℂ) * (x : ℂ) ^ 2) := by
  ext x
  unfold gauss
  rw [Complex.ofReal_exp]
  congr 1
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

lemma gauss_integrable (a : ℝ) (ha : 0 < a) : Integrable (gauss a) := by
  rw [gauss_eq a ha]
  have hb : 0 < (((a ^ 2 / π : ℝ)) : ℂ).re := by
    simp only [Complex.ofReal_re]; positivity
  have := integrable_cexp_neg_mul_sq (b := π * (((a ^ 2 / π : ℝ)) : ℂ)) (by
    simp only [Complex.re_ofReal_mul]; positivity)
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [neg_mul]

lemma fourier_gauss (a : ℝ) (ha : 0 < a) :
    𝓕 (gauss a) = fun t : ℝ => (((√π / a : ℝ)) : ℂ) * gauss (π / a) t := by
  rw [gauss_eq a ha]
  have hb : 0 < (((a ^ 2 / π : ℝ)) : ℂ).re := by
    simp only [Complex.ofReal_re]; positivity
  rw [fourier_gaussian_pi hb]
  ext t
  have h1 : (((a ^ 2 / π : ℝ)) : ℂ) ^ (1 / 2 : ℂ) = (((a / √π : ℝ)) : ℂ) := by
    have e : (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) := by push_cast; ring
    rw [e, ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow,
      Real.sqrt_div (sq_nonneg a), Real.sqrt_sq ha.le]
  rw [h1]
  unfold gauss
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hs : (√π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [Complex.ofReal_exp]
  push_cast
  congr 1
  · field_simp
  · congr 1
    field_simp

lemma key (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ, (((Real.exp (-(a * x) ^ 2) / Real.cosh (π * x) : ℝ)) : ℂ)
      = (((√π / a : ℝ)) : ℂ) *
        ∫ x : ℝ, (((Real.exp (-((π / a) * x) ^ 2) / Real.cosh (π * x) : ℝ)) : ℂ) := by
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    ext x y; simp [real_inner_comm]
  have h0 := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner SechFT.sech_integrable (gauss_integrable a ha)
  rw [hflip] at h0
  have h : ∫ ξ, (𝓕 (fun x : ℝ => (((Real.cosh (π * x))⁻¹ : ℝ) : ℂ)) ξ) • gauss a ξ
      = ∫ x, (((Real.cosh (π * x))⁻¹ : ℝ) : ℂ) • 𝓕 (gauss a) x := h0
  rw [SechFT.fourier_sech, fourier_gauss a ha] at h
  simp only [smul_eq_mul] at h
  have e1 : ∀ x : ℝ, (((Real.cosh (π * x))⁻¹ : ℝ) : ℂ) * gauss a x
      = (((Real.exp (-(a * x) ^ 2) / Real.cosh (π * x) : ℝ)) : ℂ) := by
    intro x; unfold gauss; push_cast; ring
  have e2 : ∀ x : ℝ, (((Real.cosh (π * x))⁻¹ : ℝ) : ℂ) * ((((√π / a : ℝ)) : ℂ) * gauss (π / a) x)
      = (((√π / a : ℝ)) : ℂ) * (((Real.exp (-((π / a) * x) ^ 2) / Real.cosh (π * x) : ℝ)) : ℂ) := by
    intro x; unfold gauss; push_cast; ring
  simp only [e1, e2] at h
  rw [h, integral_const_mul]

lemma key_real (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ, Real.exp (-(a * x) ^ 2) / Real.cosh (π * x)
      = √π / a * ∫ x : ℝ, Real.exp (-((π / a) * x) ^ 2) / Real.cosh (π * x) := by
  have h := key a ha
  have h1 : ∫ x : ℝ, (((Real.exp (-(a * x) ^ 2) / Real.cosh (π * x) : ℝ)) : ℂ)
      = ((∫ x : ℝ, Real.exp (-(a * x) ^ 2) / Real.cosh (π * x) : ℝ) : ℂ) := integral_ofReal
  have h2 : ∫ x : ℝ, (((Real.exp (-((π / a) * x) ^ 2) / Real.cosh (π * x) : ℝ)) : ℂ)
      = ((∫ x : ℝ, Real.exp (-((π / a) * x) ^ 2) / Real.cosh (π * x) : ℝ) : ℂ) := integral_ofReal
  rw [h1, h2] at h
  exact_mod_cast h

lemma half (a : ℝ) :
    ∫ x : ℝ, Real.exp (-(a * x) ^ 2) / Real.cosh (π * x)
      = 2 * ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(a * x) ^ 2) / Real.cosh (π * x) := by
  rw [← integral_comp_abs (f := fun y : ℝ => Real.exp (-(a * y) ^ 2) / Real.cosh (π * y))]
  congr 1
  ext x
  have h1 : π * |x| = |π * x| := by rw [abs_mul, abs_of_pos Real.pi_pos]
  have h2 : (a * |x|) ^ 2 = (a * x) ^ 2 := by rw [mul_pow, sq_abs, mul_pow]
  simp only [h1, h2, Real.cosh_abs]

end GaussSech

open GaussSech in
theorem solution (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hαβ : α * β = Real.pi) :
    Real.sqrt α * (∫ x in Set.Ioi (0 : ℝ),
      Real.exp (-(α * x) ^ 2) / Real.cosh (Real.pi * x))
      = Real.sqrt β * (∫ x in Set.Ioi (0 : ℝ),
      Real.exp (-(β * x) ^ 2) / Real.cosh (Real.pi * x)) := by
  have hβ' : β = π / α := by field_simp; linarith
  have k := key_real α hα
  rw [half α, half (π / α)] at k
  rw [← hβ'] at k
  have k' : ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(α * x) ^ 2) / Real.cosh (π * x)
      = √π / α * ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(β * x) ^ 2) / Real.cosh (π * x) := by
    linarith
  rw [k']
  have hsa : √α * √α = α := Real.mul_self_sqrt hα.le
  have hsb : √β = √π / √α := by
    rw [hβ', Real.sqrt_div Real.pi_pos.le]
  have hsa0 : 0 < √α := Real.sqrt_pos.mpr hα
  have c : √α * (√π / α) = √π / √α := by
    obtain ⟨t, ht⟩ : ∃ t, t = √α := ⟨_, rfl⟩
    rw [← ht] at hsa hsa0 ⊢
    rw [← hsa]
    field_simp
  rw [hsb, ← mul_assoc, c]
