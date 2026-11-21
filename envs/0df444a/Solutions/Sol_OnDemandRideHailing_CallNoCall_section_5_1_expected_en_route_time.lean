-- Prove2me | solution 1 for OnDemandRideHailing.CallNoCall.section_5_1_expected_en_route_time
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T02:41:01.270293+00:00
-- url     : https://prove2.me/submissions/e0585202-a4d8-4f75-9dae-259b7ff6d55f

import Mathlib

theorem solution {R v : ℝ} (hR : 0 < R) (hv : 0 < v) (m : ℕ) :
    ∫ t in (0 : ℝ)..R / v, ((R - v * t) / R) ^ m = R / (v * ((m : ℝ) + 1)) := by
  have hv0 : v ≠ 0 := hv.ne'
  have hR0 : R ≠ 0 := hR.ne'
  have hfun : ∀ t : ℝ, ((R - v * t) / R) ^ m = (((-v) * t + R) / R) ^ m := by
    intro t; congr 1; ring
  simp only [hfun]
  rw [intervalIntegral.integral_comp_mul_add (f := fun y : ℝ => (y / R) ^ m) (c := -v) (d := R)
    (by linarith)]
  have h2 : (-v) * (R / v) + R = 0 := by field_simp; ring
  simp only [mul_zero, zero_add, h2]
  rw [intervalIntegral.integral_symm]
  simp only [smul_eq_mul]
  have hpow : R ^ m * R⁻¹ ^ m = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hR0, one_pow]
  have h3 : ∀ x : ℝ, (x / R) ^ m = x ^ m * R⁻¹ ^ m := by
    intro x; rw [div_eq_mul_inv, mul_pow]
  simp only [h3]
  rw [intervalIntegral.integral_mul_const, integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero m), sub_zero]
  rw [pow_succ]
  have h4 : R ^ m * R / ((m : ℝ) + 1) * R⁻¹ ^ m = R / ((m : ℝ) + 1) := by
    rw [div_mul_eq_mul_div, show R ^ m * R * R⁻¹ ^ m = R by
      rw [mul_assoc, mul_comm R (R⁻¹ ^ m), ← mul_assoc, hpow, one_mul]]
  rw [h4]
  field_simp
