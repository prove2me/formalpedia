-- Prove2me | solution 1 for RegevLWE.GaussConv.fourier_rhoShift
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T19:16:00.488576+00:00
-- url     : https://prove2.me/submissions/1ead56ee-a0d8-4288-bdc5-92f9fdccd41b

import Mathlib
import Definitions.Def_RegevLWE_GaussConv_Gaussian
import Definitions.Def_RegevLWE_GaussConv_Lattice

open FourierTransform

open RegevLWE.GaussConv in
theorem solution {n : ℕ} {σ : ℝ} (hσ : 0 < σ) (c w : EuclideanSpace ℝ (Fin n)) :
    𝓕 (fun x : EuclideanSpace ℝ (Fin n) => (rhoShift σ c x : ℂ)) w =
      Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ c w : ℝ))) * (σ : ℂ) ^ n *
        (rho (1 / σ) w : ℂ) := by
  set g : EuclideanSpace ℝ (Fin n) → ℂ :=
    fun v => Complex.exp (-((Real.pi : ℂ) / (σ : ℂ) ^ 2) * (‖v‖ : ℂ) ^ 2) with hg
  have key : (fun x : EuclideanSpace ℝ (Fin n) => (rhoShift σ c x : ℂ)) =
      g ∘ (fun v => v + (-c)) := by
    funext x
    simp only [Function.comp_apply, hg, rhoShift, rho, Complex.ofReal_exp]
    congr 1
    rw [← sub_eq_add_neg]
    push_cast
    ring
  have htr := VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
    MeasureTheory.volume (innerₗ (EuclideanSpace ℝ (Fin n))) g (-c)
  rw [key]
  change VectorFourier.fourierIntegral Real.fourierChar MeasureTheory.volume
    (innerₗ (EuclideanSpace ℝ (Fin n))) (g ∘ fun v => v + -c) w = _
  rw [htr]
  change (Real.fourierChar (innerₗ (EuclideanSpace ℝ (Fin n)) (-c) w)) • 𝓕 g w = _
  have hb : 0 < ((Real.pi : ℂ) / (σ : ℂ) ^ 2).re := by
    rw [show ((Real.pi : ℂ) / (σ : ℂ) ^ 2) = ((Real.pi / σ ^ 2 : ℝ) : ℂ) by push_cast; rfl,
      Complex.ofReal_re]
    positivity
  rw [hg, fourier_gaussian_innerProductSpace hb, finrank_euclideanSpace_fin]
  have hσ0 : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hσ.ne'
  have hπ0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have e1 : (Real.pi : ℂ) / ((Real.pi : ℂ) / (σ : ℂ) ^ 2) = ((σ ^ 2 : ℝ) : ℂ) := by
    push_cast; field_simp
  have e2 : ((σ ^ 2 : ℝ) : ℂ) ^ ((n : ℂ) / 2) = (σ : ℂ) ^ n := by
    rw [show ((n : ℂ) / 2) = ((n / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity), ← Real.rpow_two, ← Real.rpow_mul hσ.le,
      show (2 : ℝ) * (n / 2) = n by ring, Real.rpow_natCast]
    push_cast; rfl
  have e3 : Complex.exp (-(Real.pi : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / ((Real.pi : ℂ) / (σ : ℂ) ^ 2)) =
      (rho (1 / σ) w : ℂ) := by
    simp only [rho, Complex.ofReal_exp]
    congr 1
    push_cast
    field_simp
  have hi : innerₗ (EuclideanSpace ℝ (Fin n)) (-c) w = -inner ℝ c w := by
    simp [inner_neg_left]
  rw [e1, e2, e3, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, hi]
  rw [← mul_assoc]
  congr 2
  push_cast
  ring_nf
