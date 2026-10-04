-- Prove2me | solution 1 for ReflectionlessPotential.fourier_poisson
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T20:31:48.900595+00:00
-- url     : https://prove2.me/submissions/87b5c8af-6f12-486a-aae8-cc1036005e73

import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Probability.Distributions.Cauchy

open Complex MeasureTheory Set Real
open scoped FourierTransform RealInnerProductSpace

private lemma laplace_transform (a w : ℝ) (ha : 0 < a) :
    (𝓕 (fun x : ℝ => Complex.exp (-((a * |x| : ℝ) : ℂ)) )) w =
      (2 * (a : ℂ)) / ((a : ℂ) ^ 2 + (2 * Real.pi * (w : ℂ)) ^ 2) := by
  let g : ℝ → ℂ := fun x =>
    Complex.exp ((-2 * Real.pi * x * w : ℝ) * I) * Complex.exp (-((a * |x| : ℝ) : ℂ))
  let b : ℂ := (a : ℂ) - 2 * Real.pi * w * I
  let c : ℂ := -(a : ℂ) - 2 * Real.pi * w * I
  have hb : 0 < b.re := by simpa [b] using ha
  have hc : c.re < 0 := by simpa [c] using (neg_neg_of_pos ha)
  have hneg : EqOn (fun x : ℝ => Complex.exp (b * x)) g (Iic 0) := by
    intro x hx
    dsimp [g, b]
    rw [abs_of_nonpos hx, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hpos : EqOn (fun x : ℝ => Complex.exp (c * x)) g (Ioi 0) := by
    intro x hx
    dsimp [g, c]
    rw [abs_of_pos hx, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hn := (integrableOn_exp_mul_complex_Iic hb 0).congr_fun hneg measurableSet_Iic
  have hp := (integrableOn_exp_mul_complex_Ioi hc 0).congr_fun hpos measurableSet_Ioi
  rw [fourier_real_eq_integral_exp_smul]
  change (∫ x, g x) = _
  rw [← intervalIntegral.integral_Iic_add_Ioi hn hp,
    ← setIntegral_congr_fun measurableSet_Iic hneg,
    ← setIntegral_congr_fun measurableSet_Ioi hpos,
    integral_exp_mul_complex_Iic hb, integral_exp_mul_complex_Ioi hc]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  have hd : (a : ℂ) ^ 2 + (2 * Real.pi * (w : ℂ)) ^ 2 ≠ 0 := by
    have h : 0 < a ^ 2 + (2 * Real.pi * w) ^ 2 := by positivity
    exact_mod_cast ne_of_gt h
  dsimp [b, c] at hb0 hc0 ⊢
  apply (eq_div_iff hd).mpr
  field_simp [hb0, hc0]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem solution (κ t : ℝ) (hκ : 0 < κ) :
    ∫ k : ℝ, Complex.exp (Complex.I * k * t) / ((k : ℂ) ^ 2 + (κ : ℂ) ^ 2) =
      ((Real.pi / κ * Real.exp (-(κ * |t|)) : ℝ) : ℂ) := by
  let a : ℝ := 2 * Real.pi * κ
  let f : ℝ → ℂ := fun x => Complex.exp (-((a * |x| : ℝ) : ℂ))
  have ha : 0 < a := by dsimp [a]; positivity
  have hfn : IntegrableOn f (Iic 0) := by
    refine (integrableOn_exp_mul_complex_Iic (a := (a : ℂ)) (by simpa using ha) 0).congr_fun
      (fun x hx => ?_) measurableSet_Iic
    simp [f, abs_of_nonpos (show x ≤ 0 from hx)]
  have hfp : IntegrableOn f (Ioi 0) := by
    refine (integrableOn_exp_mul_complex_Ioi (a := -(a : ℂ)) (by simpa using ha) 0).congr_fun
      (fun x hx => ?_) measurableSet_Ioi
    simp [f, abs_of_pos (show 0 < x from hx)]
  have hf : Integrable f := by
    have h := hfn.union hfp
    simpa only [Iic_union_Ioi, integrableOn_univ] using h
  have hformula (w : ℝ) : 𝓕 f w =
      ((κ / Real.pi : ℝ) : ℂ) / ((w : ℂ) ^ 2 + (κ : ℂ) ^ 2) := by
    rw [show f = (fun x : ℝ => Complex.exp (-((a * |x| : ℝ) : ℂ))) from rfl,
      laplace_transform a w ha]
    have hd : (w : ℂ) ^ 2 + (κ : ℂ) ^ 2 ≠ 0 := by
      have h : 0 < w ^ 2 + κ ^ 2 := by positivity
      exact_mod_cast ne_of_gt h
    dsimp [a]
    push_cast
    have hd' : (κ : ℂ) ^ 2 + (w : ℂ) ^ 2 ≠ 0 := by simpa [add_comm] using hd
    field_simp [hd, hd', Real.pi_ne_zero]
    ring
  have hF : Integrable (𝓕 f) := by
    have hreal (w : ℝ) : ProbabilityTheory.cauchyPDFReal 0 ⟨κ, hκ.le⟩ w =
        (κ / Real.pi) / (w ^ 2 + κ ^ 2) := by
      change Real.pi⁻¹ * κ * ((w - 0) ^ 2 + κ ^ 2)⁻¹ = _
      simp only [sub_zero]
      ring
    have h := (ProbabilityTheory.integrable_cauchyPDFReal 0 (γ := ⟨κ, hκ.le⟩)).ofReal (𝕜 := ℂ)
    simp_rw [hreal] at h
    convert h using 1
    ext w
    rw [hformula]
    push_cast
    rfl
  have hc : Continuous f := by dsimp [f]; fun_prop
  have hi := hf.fourierInv_fourier_eq hF (v := t / (2 * Real.pi)) hc.continuousAt
  rw [fourierInv_eq'] at hi
  simp only [Real.inner_apply, smul_eq_mul] at hi
  simp_rw [hformula] at hi
  have he (w : ℝ) :
      Complex.exp ((2 * Real.pi * (w * (t / (2 * Real.pi))) : ℝ) * I) *
        (((κ / Real.pi : ℝ) : ℂ) / ((w : ℂ) ^ 2 + (κ : ℂ) ^ 2)) =
      ((κ / Real.pi : ℝ) : ℂ) *
        (Complex.exp (I * w * t) / ((w : ℂ) ^ 2 + (κ : ℂ) ^ 2)) := by
    have hr : 2 * Real.pi * (w * (t / (2 * Real.pi))) = w * t := by
      field_simp
    rw [hr]
    push_cast
    rw [show (w : ℂ) * t * I = I * w * t by ring]
    ring
  simp_rw [he] at hi
  rw [integral_const_mul] at hi
  have hv : f (t / (2 * Real.pi)) = (Real.exp (-(κ * |t|)) : ℂ) := by
    dsimp [f, a]
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi),
      ← Complex.ofReal_neg, ← Complex.ofReal_exp]
    congr 1
    field_simp
  rw [hv] at hi
  have hk0 : (κ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hκ
  have hp0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast at hi ⊢
  apply (mul_left_cancel₀ (div_ne_zero hk0 hp0))
  rw [hi]
  field_simp
