-- Prove2me | solution 1 for TeschlQM.Free.fourier_schwartz_bijective
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:52:54.793346+00:00
-- url     : https://prove2.me/submissions/835cb0a6-e50f-4875-8d7b-5ca91516b7d6

import Mathlib
import Definitions.Def_TeschlQM_Free_fourier

open MeasureTheory FourierTransform SchwartzMap
open scoped InnerProductSpace

namespace TeschlQM.Free

variable {n : ℕ}

/-- The normalization constant `(2π)^{-n/2}`. -/
noncomputable def Kc_core (n : ℕ) : ℝ := (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ))⁻¹

lemma two_pi_pos_core : (0 : ℝ) < 2 * Real.pi := by positivity

/-- `K² (2π)^n = 1`. -/
lemma Kc_sq_core (n : ℕ) : (Kc_core n : ℂ) * ((Kc_core n : ℂ) * ((2 * Real.pi) ^ n : ℝ)) = 1 := by
  have h2 : ((2 * Real.pi) ^ ((n : ℝ) / 2)) ^ 2 = (2 * Real.pi) ^ n := by
    rw [← Real.rpow_two, ← Real.rpow_mul two_pi_pos_core.le,
      show ((n : ℝ) / 2 * 2) = (n : ℝ) by ring, Real.rpow_natCast]
  have hpos : (0 : ℝ) < (2 * Real.pi) ^ ((n : ℝ) / 2) := Real.rpow_pos_of_pos two_pi_pos_core _
  have : Kc_core n * (Kc_core n * (2 * Real.pi) ^ n) = 1 := by
    rw [← h2, Kc_core]; field_simp
  exact_mod_cast this

/-- Teschl's transform in terms of Mathlib's `𝓕`. -/
lemma fourier_eq_core (f : EuclideanSpace ℝ (Fin n) → ℂ) (p : EuclideanSpace ℝ (Fin n)) :
    fourier n f p = (Kc_core n : ℂ) * 𝓕 f ((2 * Real.pi)⁻¹ • p) := by
  unfold fourier Kc_core
  rw [Real.fourier_eq', Complex.ofReal_inv]
  congr 1
  congr 1
  funext x
  rw [smul_eq_mul, real_inner_smul_right, real_inner_comm]
  congr 2
  push_cast
  field_simp

/-- Teschl's inverse transform in terms of Mathlib's `𝓕⁻`. -/
lemma fourierInv_eq_core (g : EuclideanSpace ℝ (Fin n) → ℂ) (x : EuclideanSpace ℝ (Fin n)) :
    fourierInv n g x = (Kc_core n : ℂ) * 𝓕⁻ g ((2 * Real.pi)⁻¹ • x) := by
  unfold fourierInv Kc_core
  rw [Real.fourierInv_eq', Complex.ofReal_inv]
  congr 1
  congr 1
  funext p
  rw [smul_eq_mul, real_inner_smul_right]
  congr 2
  push_cast
  field_simp

/-- Scaling: `𝓕 (K h(·/2π)) (w) = K (2π)^n 𝓕 h (2π w)`. -/
lemma fourier_scale_core (h : EuclideanSpace ℝ (Fin n) → ℂ) (w : EuclideanSpace ℝ (Fin n)) :
    𝓕 (fun p => (Kc_core n : ℂ) * h ((2 * Real.pi)⁻¹ • p)) w =
      (Kc_core n : ℂ) * (((2 * Real.pi) ^ n : ℝ) * 𝓕 h ((2 * Real.pi) • w)) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  set G : EuclideanSpace ℝ (Fin n) → ℂ := fun u =>
    Complex.exp (↑(-2 * Real.pi * ⟪u, (2 * Real.pi) • w⟫_ℝ) * Complex.I) • h u with hG
  have hpt : ∀ v, Complex.exp (↑(-2 * Real.pi * ⟪v, w⟫_ℝ) * Complex.I) •
      ((Kc_core n : ℂ) * h ((2 * Real.pi)⁻¹ • v)) = (Kc_core n : ℂ) * G ((2 * Real.pi)⁻¹ • v) := by
    intro v
    simp only [hG, smul_eq_mul, real_inner_smul_left, real_inner_smul_right]
    rw [mul_inv_cancel_left₀ two_pi_pos_core.ne']
    ring
  simp_rw [hpt]
  rw [integral_const_mul, Measure.integral_comp_inv_smul volume G (2 * Real.pi),
    finrank_euclideanSpace_fin, abs_of_pos (pow_pos two_pi_pos_core n), Complex.real_smul]

/-- Scaling for the inverse transform. -/
lemma fourierInv_scale_core (h : EuclideanSpace ℝ (Fin n) → ℂ) (w : EuclideanSpace ℝ (Fin n)) :
    𝓕⁻ (fun p => (Kc_core n : ℂ) * h ((2 * Real.pi)⁻¹ • p)) w =
      (Kc_core n : ℂ) * (((2 * Real.pi) ^ n : ℝ) * 𝓕⁻ h ((2 * Real.pi) • w)) := by
  rw [Real.fourierInv_eq', Real.fourierInv_eq']
  set G : EuclideanSpace ℝ (Fin n) → ℂ := fun u =>
    Complex.exp (↑(2 * Real.pi * ⟪u, (2 * Real.pi) • w⟫_ℝ) * Complex.I) • h u with hG
  have hpt : ∀ v, Complex.exp (↑(2 * Real.pi * ⟪v, w⟫_ℝ) * Complex.I) •
      ((Kc_core n : ℂ) * h ((2 * Real.pi)⁻¹ • v)) = (Kc_core n : ℂ) * G ((2 * Real.pi)⁻¹ • v) := by
    intro v
    simp only [hG, smul_eq_mul, real_inner_smul_left, real_inner_smul_right]
    rw [mul_inv_cancel_left₀ two_pi_pos_core.ne']
    ring
  simp_rw [hpt]
  rw [integral_const_mul, Measure.integral_comp_inv_smul volume G (2 * Real.pi),
    finrank_euclideanSpace_fin, abs_of_pos (pow_pos two_pi_pos_core n), Complex.real_smul]

/-- The scaling `p ↦ (2π)⁻¹ • p` as a continuous linear equivalence. -/
noncomputable def scaleEquiv_core (n : ℕ) : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin n)) (2 * Real.pi)⁻¹
    (inv_ne_zero two_pi_pos_core.ne')).toContinuousLinearEquiv

lemma scaleEquiv_core_apply (p : EuclideanSpace ℝ (Fin n)) :
    scaleEquiv_core n p = (2 * Real.pi)⁻¹ • p := by
  simp [scaleEquiv_core]

/-- Teschl's transform of a Schwartz function is a Schwartz function. -/
lemma fourier_schwartz_core (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
    ∃ g : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ, ⇑g = fourier n f := by
  refine ⟨(Kc_core n : ℂ) • compCLMOfContinuousLinearEquiv ℂ (scaleEquiv_core n) (𝓕 f), ?_⟩
  funext p
  rw [fourier_eq_core]
  simp only [smul_apply, compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    scaleEquiv_core_apply, fourier_coe, smul_eq_mul]

/-- Teschl's inverse transform of a Schwartz function is a Schwartz function. -/
lemma fourierInv_schwartz_core (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
    ∃ g : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ, ⇑g = fourierInv n f := by
  refine ⟨(Kc_core n : ℂ) • compCLMOfContinuousLinearEquiv ℂ (scaleEquiv_core n) (𝓕⁻ f), ?_⟩
  funext p
  rw [fourierInv_eq_core]
  simp only [smul_apply, compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    scaleEquiv_core_apply, fourierInv_coe, smul_eq_mul]

lemma integrable_fourier_core (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
    Integrable (𝓕 ⇑f) volume := by
  rw [← fourier_coe]; exact (𝓕 f).integrable

/-- Inversion in Teschl's normalization. -/
lemma inv_core (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
    fourierInv n (fourier n f) = ⇑f ∧ fourier n (fourierInv n f) = ⇑f := by
  constructor
  · funext x
    rw [fourierInv_eq_core]
    have : fourier n ⇑f = fun p => (Kc_core n : ℂ) * 𝓕 ⇑f ((2 * Real.pi)⁻¹ • p) := by
      funext p; exact fourier_eq_core _ _
    rw [this, fourierInv_scale_core, smul_inv_smul₀ two_pi_pos_core.ne',
      f.continuous.fourierInv_fourier_eq f.integrable (integrable_fourier_core f),
      ← mul_assoc, ← mul_assoc, mul_assoc (Kc_core n : ℂ), Kc_sq_core, one_mul]
  · funext x
    rw [fourier_eq_core]
    have : fourierInv n ⇑f = fun p => (Kc_core n : ℂ) * 𝓕⁻ ⇑f ((2 * Real.pi)⁻¹ • p) := by
      funext p; exact fourierInv_eq_core _ _
    rw [this, fourier_scale_core, smul_inv_smul₀ two_pi_pos_core.ne',
      f.continuous.fourier_fourierInv_eq f.integrable (integrable_fourier_core f),
      ← mul_assoc, ← mul_assoc, mul_assoc (Kc_core n : ℂ), Kc_sq_core, one_mul]

/-- `F² f (x) = f (-x)`. -/
lemma double_core (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (x : EuclideanSpace ℝ (Fin n)) :
    fourier n (fourier n f) x = f (-x) := by
  rw [fourier_eq_core]
  have : fourier n ⇑f = fun p => (Kc_core n : ℂ) * 𝓕 ⇑f ((2 * Real.pi)⁻¹ • p) := by
    funext p; exact fourier_eq_core _ _
  rw [this, fourier_scale_core, smul_inv_smul₀ two_pi_pos_core.ne',
    ← mul_assoc, ← mul_assoc, mul_assoc (Kc_core n : ℂ), Kc_sq_core, one_mul]
  have h := f.continuous.fourierInv_fourier_eq f.integrable (integrable_fourier_core f)
  have h2 : 𝓕 (𝓕 ⇑f) x = 𝓕⁻ (𝓕 ⇑f) (-x) := by
    rw [Real.fourierInv_eq_fourier_neg, neg_neg]
  rw [h2, h]

end TeschlQM.Free

open TeschlQM.Free in
theorem solution (n : ℕ) :
    (∀ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
        ∃ g : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ, ⇑g = fourier n f) ∧
      (∀ g : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
        ∃ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ, fourier n f = ⇑g) ∧
      (∀ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
        fourierInv n (fourier n f) = ⇑f ∧ fourier n (fourierInv n f) = ⇑f) ∧
      (∀ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ, ∀ x, fourier n (fourier n f) x = f (-x)) ∧
      (∀ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
        fourier n (fourier n (fourier n (fourier n f))) = ⇑f) := by
  refine ⟨fourier_schwartz_core, ?_, inv_core, double_core, ?_⟩
  · intro g
    obtain ⟨f, hf⟩ := fourierInv_schwartz_core g
    exact ⟨f, by rw [hf]; exact (inv_core g).2⟩
  · intro f
    -- `f ∘ neg` as a Schwartz function
    let f' : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ :=
      compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) f
    have hf' : ⇑f' = fun x => f (-x) := by
      funext x; simp [f']
    have h2 : fourier n (fourier n f) = ⇑f' := by
      funext x; rw [double_core, hf']
    rw [h2]
    funext x
    rw [double_core, hf']
    show f (- -x) = f x
    rw [neg_neg]

#print axioms solution
