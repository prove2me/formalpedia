-- Prove2me | solution 1 for RybinAI2026.P01.psi_ge_atan_div_sqrt_of_one_lt_r16
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T10:01:14.438354+00:00
-- url     : https://prove2.me/submissions/78d0fba7-eedf-4481-b42a-5f118d67921f

import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem solution (t : ℝ) (ht : 1 < t) :
    (Real.arctan (Real.sqrt t)) / Real.sqrt t ≤ ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹ := by
  have ht0 : 0 < t := by linarith
  have hsq : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  have heval : (∫ s in (0 : ℝ)..1, (1 + t * s ^ 2)⁻¹)
      = Real.arctan (Real.sqrt t) / Real.sqrt t := by
    have h1 : (fun s : ℝ => (1 + t * s ^ 2)⁻¹)
        = fun s : ℝ => (fun x : ℝ => (1 + x ^ 2)⁻¹) (Real.sqrt t * s) := by
      funext s
      simp only
      congr 1
      rw [mul_pow, Real.sq_sqrt ht0.le]
    rw [h1, intervalIntegral.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) hsq.ne',
      integral_inv_one_add_sq]
    simp [div_eq_inv_mul]
  rw [← heval]
  apply intervalIntegral.integral_mono_on zero_le_one
  · apply Continuous.intervalIntegrable
    apply Continuous.inv₀ (by fun_prop)
    intro s; positivity
  · apply Continuous.intervalIntegrable
    apply Continuous.inv₀ (by fun_prop)
    intro s
    have : 0 ≤ (t - 1) * s ^ 2 := mul_nonneg (by linarith) (sq_nonneg s)
    linarith
  · intro s _
    have h0 : 0 < 1 + (t - 1) * s ^ 2 := by
      have : 0 ≤ (t - 1) * s ^ 2 := mul_nonneg (by linarith) (sq_nonneg s)
      linarith
    apply inv_anti₀ h0
    nlinarith [sq_nonneg s]
