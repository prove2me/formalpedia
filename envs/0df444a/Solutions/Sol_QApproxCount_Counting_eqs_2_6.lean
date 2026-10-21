-- Prove2me | solution 1 for QApproxCount.Counting.eqs_2_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:32:43.695348+00:00
-- url     : https://prove2.me/submissions/dbcd0edf-36d4-4407-80e3-a55b394902ec

import Mathlib
set_option autoImplicit false

theorem solution (θ : ℝ) (hθ : 0 < θ) (k₀ kend : ℕ)
    (hk₀ : θ * (1.05 : ℝ) ^ k₀ ≤ 0.9) (hk₀max : 0.9 < θ * (1.05 : ℝ) ^ (k₀ + 1))
    (hlo : k₀ + 1 ≤ kend) (hhi : kend ≤ k₀ + 10) :
    0.9 * (1.05 : ℝ) ^ (-(kend : ℤ)) ≤ θ ∧ θ ≤ 1.65 * (0.9 * (1.05 : ℝ) ^ (-(kend : ℤ))) := by
  have hp : (0:ℝ) < 1.05 ^ kend := by positivity
  have e : (1.05 : ℝ) ^ (-(kend : ℤ)) = ((1.05 : ℝ) ^ kend)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  rw [e]
  have h1 : (1.05 : ℝ) ^ (k₀ + 1) ≤ 1.05 ^ kend := pow_le_pow_right₀ (by norm_num) hlo
  have h2 : (1.05 : ℝ) ^ kend ≤ 1.05 ^ (k₀ + 10) := pow_le_pow_right₀ (by norm_num) hhi
  have h3 : (1.05 : ℝ) ^ (k₀ + 10) = 1.05 ^ k₀ * 1.05 ^ 10 := pow_add _ _ _
  have h4 : (1.05 : ℝ) ^ 10 ≤ 1.63 := by norm_num
  have h5 : 0.9 < θ * 1.05 ^ kend := lt_of_lt_of_le hk₀max (mul_le_mul_of_nonneg_left h1 hθ.le)
  have h6 : θ * 1.05 ^ kend ≤ 0.9 * 1.63 := by
    calc θ * 1.05 ^ kend ≤ θ * (1.05 ^ k₀ * 1.05 ^ 10) := by
          rw [← h3]; exact mul_le_mul_of_nonneg_left h2 hθ.le
      _ = (θ * 1.05 ^ k₀) * 1.05 ^ 10 := by ring
      _ ≤ 0.9 * 1.63 := by
          apply mul_le_mul hk₀ h4 (by positivity) (by norm_num)
  constructor
  · rw [← div_eq_mul_inv, div_le_iff₀ hp]; linarith
  · rw [← div_eq_mul_inv, ← mul_div_assoc, le_div_iff₀ hp]; linarith
