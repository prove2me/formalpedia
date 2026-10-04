-- Prove2me | solution 1 for ReflectionlessPotential.fourier_sechSq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T21:35:43.196143+00:00
-- url     : https://prove2.me/submissions/96e605d1-442e-4799-ad50-bc26db4bec43

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.Jacobian

open Complex MeasureTheory Set

private noncomputable def logistic (κ x : ℝ) : ℝ := Real.exp (2 * κ * x) / (1 + Real.exp (2 * κ * x))

private lemma logistic_mem (κ x : ℝ) : logistic κ x ∈ Ioo 0 1 := by
  have he := Real.exp_pos (2 * κ * x)
  constructor
  · exact div_pos he (by positivity)
  · apply (div_lt_one (by positivity : 0 < 1 + Real.exp (2 * κ * x))).mpr
    linarith

private lemma logistic_ratio (κ x : ℝ) :
    logistic κ x / (1 - logistic κ x) = Real.exp (2 * κ * x) := by
  dsimp [logistic]
  have he := Real.exp_pos (2 * κ * x)
  field_simp
  ring

private lemma logistic_image (κ : ℝ) (hκ : 0 < κ) :
    (fun x => logistic κ x) '' (univ : Set ℝ) = Ioo 0 1 := by
  ext t
  constructor
  · rintro ⟨x, _, rfl⟩
    exact logistic_mem κ x
  · intro ht
    let x := Real.log (t / (1 - t)) / (2 * κ)
    refine ⟨x, mem_univ _, ?_⟩
    have hr : 0 < t / (1 - t) := div_pos ht.1 (sub_pos.mpr ht.2)
    have hexp : Real.exp (2 * κ * x) = t / (1 - t) := by
      dsimp [x]
      rw [mul_div_cancel₀ _ (by positivity : 2 * κ ≠ 0), Real.exp_log hr]
    dsimp [logistic]
    rw [hexp]
    have hd : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht.2)
    field_simp [hd]
    ring

private lemma logistic_injective (κ : ℝ) (hκ : 0 < κ) :
    Function.Injective (logistic κ) := by
  intro x y h
  have he : Real.exp (2 * κ * x) = Real.exp (2 * κ * y) := by
    rw [← logistic_ratio κ x, ← logistic_ratio κ y, h]
  exact (mul_left_cancel₀ (by positivity : 2 * κ ≠ 0)) (Real.exp_injective he)

private lemma logistic_deriv (κ x : ℝ) :
    HasDerivAt (logistic κ)
      (2 * κ * Real.exp (2 * κ * x) / (1 + Real.exp (2 * κ * x)) ^ 2) x := by
  have he := ((hasDerivAt_id x).const_mul (2 * κ)).exp
  have hd := he.div (he.const_add 1) (by positivity : 1 + Real.exp (2 * κ * x) ≠ 0)
  simp only [id_eq, mul_one] at hd
  convert hd using 1
  all_goals first | rfl | ring

private lemma span_det (d : ℝ) :
    (ContinuousLinearMap.toSpanSingleton ℝ d : ℝ →ₗ[ℝ] ℝ).det = d := by
  have he : (ContinuousLinearMap.toSpanSingleton ℝ d : ℝ →ₗ[ℝ] ℝ) =
      d • LinearMap.id := by
    ext
    simp
  rw [he, LinearMap.det_smul, LinearMap.det_id]
  simp

private lemma logistic_deriv_cosh (κ x : ℝ) :
    2 * κ * Real.exp (2 * κ * x) / (1 + Real.exp (2 * κ * x)) ^ 2 =
      κ / (2 * Real.cosh (κ * x) ^ 2) := by
  rw [show 2 * κ * x = κ * x + κ * x by ring, Real.exp_add,
    Real.cosh_eq, Real.exp_neg]
  have he := Real.exp_pos (κ * x)
  field_simp
  ring

private lemma logistic_beta (κ k x : ℝ) (hκ : 0 < κ) :
    (logistic κ x : ℂ) ^ ((1 + (k / (2 * κ) : ℝ) * I) - 1) *
      (1 - (logistic κ x : ℂ)) ^ ((1 - (k / (2 * κ) : ℝ) * I) - 1) =
        Complex.exp (I * k * x) := by
  have hu := logistic_mem κ x
  have hr : 0 < 1 - logistic κ x := sub_pos.mpr hu.2
  have hlog : Real.log (logistic κ x) - Real.log (1 - logistic κ x) = 2 * κ * x := by
    rw [← Real.log_div (ne_of_gt hu.1) (ne_of_gt hr), logistic_ratio, Real.log_exp]
  rw [show (1 : ℂ) + (k / (2 * κ) : ℝ) * I - 1 = (k / (2 * κ) : ℝ) * I by ring,
    show (1 : ℂ) - (k / (2 * κ) : ℝ) * I - 1 = -((k / (2 * κ) : ℝ) * I) by ring]
  have hu0 : (logistic κ x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu.1
  have hr0 : ((1 - logistic κ x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  rw [show (1 : ℂ) - logistic κ x = ((1 - logistic κ x : ℝ) : ℂ) by push_cast; rfl,
    Complex.cpow_def_of_ne_zero hu0, Complex.cpow_def_of_ne_zero hr0,
    ← Complex.ofReal_log hu.1.le, ← Complex.ofReal_log hr.le, ← Complex.exp_add]
  congr 1
  calc
    _ = ((Real.log (logistic κ x) - Real.log (1 - logistic κ x) : ℝ) : ℂ) *
        ((k / (2 * κ) : ℝ) : ℂ) * I := by push_cast; ring
    _ = _ := by
      rw [hlog]
      push_cast
      have hk0 : (κ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hκ
      field_simp [hk0]

private lemma beta_imag (q : ℝ) (hq : q ≠ 0) :
    Complex.betaIntegral (1 + (q : ℂ) * I) (1 - (q : ℂ) * I) =
      ((Real.pi * q / Real.sinh (Real.pi * q) : ℝ) : ℂ) := by
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simp) (by simp)]
  have hg2 : Complex.Gamma 2 = 1 := by
    rw [show (2 : ℂ) = 1 + 1 by norm_num, Complex.Gamma_add_one 1 one_ne_zero,
      Complex.Gamma_one, mul_one]
  have hadd : (1 + (q : ℂ) * I) + (1 - (q : ℂ) * I) = 2 := by ring
  rw [hadd, hg2, div_one, add_comm 1,
    Complex.Gamma_add_one _ (mul_ne_zero (by exact_mod_cast hq) I_ne_zero),
    mul_assoc, Complex.Gamma_mul_Gamma_one_sub]
  rw [show (Real.pi : ℂ) * ((q : ℂ) * I) = ((Real.pi * q : ℝ) : ℂ) * I by push_cast; ring,
    Complex.sin_mul_I, ← Complex.ofReal_sinh]
  push_cast
  field_simp

theorem solution (κ k : ℝ) (hκ : 0 < κ) (hk : k ≠ 0) :
    ∫ x : ℝ, Complex.exp (Complex.I * k * x) / (Real.cosh (κ * x) : ℂ) ^ 2 =
      ((Real.pi * k / (κ ^ 2 * Real.sinh (Real.pi * k / (2 * κ))) : ℝ) : ℂ) := by
  let q : ℝ := k / (2 * κ)
  let g : ℝ → ℂ := fun t => (t : ℂ) ^ ((1 + (q : ℂ) * I) - 1) *
      (1 - (t : ℂ)) ^ ((1 - (q : ℂ) * I) - 1)
  let d : ℝ → ℝ := fun x => 2 * κ * Real.exp (2 * κ * x) / (1 + Real.exp (2 * κ * x)) ^ 2
  have hd (x : ℝ) : 0 < d x := by dsimp [d]; positivity
  have hdiff (x : ℝ) (_hx : x ∈ (univ : Set ℝ)) :
      HasFDerivWithinAt (logistic κ) (ContinuousLinearMap.toSpanSingleton ℝ (d x)) univ x :=
    (logistic_deriv κ x).hasFDerivAt.hasFDerivWithinAt
  have hi := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ hdiff
    (logistic_injective κ hκ).injOn g
  rw [logistic_image κ hκ, Measure.restrict_univ] at hi
  have he (x : ℝ) : |(ContinuousLinearMap.toSpanSingleton ℝ (d x) : ℝ →ₗ[ℝ] ℝ).det| •
      g (logistic κ x) = ((κ / 2 : ℝ) : ℂ) *
        (Complex.exp (I * k * x) / (Real.cosh (κ * x) : ℂ) ^ 2) := by
    rw [span_det, abs_of_pos (hd x)]
    change d x • ((logistic κ x : ℂ) ^ ((1 + (q : ℂ) * I) - 1) *
      (1 - (logistic κ x : ℂ)) ^ ((1 - (q : ℂ) * I) - 1)) = _
    rw [logistic_beta κ k x hκ]
    simp only [RCLike.real_smul_eq_coe_mul, RCLike.ofReal_eq_complex_ofReal]
    dsimp [d]
    rw [logistic_deriv_cosh]
    push_cast
    ring
  simp_rw [he] at hi
  rw [integral_const_mul] at hi
  have hbeta : Complex.betaIntegral (1 + (q : ℂ) * I) (1 - (q : ℂ) * I) =
      ∫ t in Ioo 0 1, g t := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
  have hq : q ≠ 0 := div_ne_zero hk (by positivity)
  rw [← hbeta, beta_imag q hq] at hi
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at hi
  have hk0 : (κ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hκ
  apply (mul_left_cancel₀ (div_ne_zero hk0 (by norm_num : (2 : ℂ) ≠ 0)))
  rw [← hi]
  dsimp [q]
  push_cast
  rw [show (Real.pi : ℂ) * ((k : ℂ) / (2 * κ)) = Real.pi * k / (2 * κ) by ring]
  field_simp [hk0]
