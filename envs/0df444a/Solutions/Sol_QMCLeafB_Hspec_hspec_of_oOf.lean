-- Prove2me | solution 1 for QMCLeafB_Hspec_hspec_of_oOf
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T06:28:06.477113+00:00
-- url     : https://prove2.me/submissions/58255dec-58d4-4fb9-a629-8de8a4a81840

import Mathlib

/-- `((m-1)/m)^m ≤ 1/2` for `m ≥ 2`, via Bernoulli's inequality applied to
`1 + 1/(m-1) = (m/(m-1))`. -/
theorem solution (m : ℕ) (hm : 2 ≤ m) : (((m - 1 : ℕ) : ℚ) / (m : ℚ)) ^ m ≤ 1 / 2 := by
  have hm0 : 0 < m := by omega
  have hmQ : (0:ℚ) < (m:ℚ) := by exact_mod_cast hm0
  have hm1Q : (0:ℚ) < ((m - 1 : ℕ) : ℚ) := by
    have : 0 < m - 1 := by omega
    exact_mod_cast this
  have hcast : ((m - 1 : ℕ) : ℚ) = (m:ℚ) - 1 := by
    have h1 : 1 ≤ m := by omega
    push_cast [h1]
    ring
  set a : ℚ := ((m - 1 : ℕ) : ℚ) / (m : ℚ) with ha
  have ha_pos : 0 < a := div_pos hm1Q hmQ
  have hd : (0:ℚ) < (m:ℚ) - 1 := by
    rw [← hcast]
    exact hm1Q
  have h_inv : a⁻¹ = 1 + 1 / ((m:ℚ) - 1) := by
    rw [ha, hcast]
    field_simp
    ring
  have hBern : 1 + (m:ℚ) * (1 / ((m:ℚ) - 1)) ≤ (1 + 1 / ((m:ℚ) - 1)) ^ m := by
    have hx : (-2:ℚ) ≤ 1 / ((m:ℚ) - 1) := by
      have : (0:ℚ) ≤ 1 / ((m:ℚ) - 1) := div_nonneg zero_le_one hd.le
      linarith
    have h := one_add_mul_le_pow (R := ℚ) (a := 1 / ((m:ℚ) - 1)) (n := m) hx
    simpa [mul_comm] using h
  have htwo : (2:ℚ) ≤ 1 + (m:ℚ) * (1 / ((m:ℚ) - 1)) := by
    field_simp
    nlinarith
  have hmain : (2:ℚ) ≤ (a ^ m)⁻¹ := by
    rw [← h_inv, inv_pow] at hBern
    linarith
  have hpow_pos : (0:ℚ) < a ^ m := pow_pos ha_pos m
  have hmul : 2 * a ^ m ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hmain hpow_pos.le
    rwa [inv_mul_cancel₀ hpow_pos.ne'] at this
  linarith
