-- Prove2me | solution 1 for QMCLeafB_IterBound_pow_pred_div_self_le_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T15:15:13.515292+00:00
-- url     : https://prove2.me/submissions/f78e2ee6-f2f2-4c8c-ae27-011ec19dfb3d

import Mathlib

theorem solution (m : ℕ) (hm : 2 ≤ m) : (((m - 1 : ℕ) : ℚ) / (m : ℚ)) ^ m ≤ 1 / 2 := by
  have hm0 : (0 : ℚ) < (m : ℚ) := by
    have h : 0 < m := by omega
    exact_mod_cast h
  have hm1 : (0 : ℚ) < ((m - 1 : ℕ) : ℚ) := by
    have h : 0 < m - 1 := by omega
    exact_mod_cast h
  have hcast : ((m - 1 : ℕ) : ℚ) + 1 = (m : ℚ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ m)]
    ring
  have hbern : 1 + (m : ℚ) * (1 / ((m - 1 : ℕ) : ℚ)) ≤ (1 + 1 / ((m - 1 : ℕ) : ℚ)) ^ m := by
    apply one_add_mul_le_pow
    · have h : (0 : ℚ) < 1 / ((m - 1 : ℕ) : ℚ) := by positivity
      linarith
  have hgeom : (1 + 1 / ((m - 1 : ℕ) : ℚ)) = (m : ℚ) / ((m - 1 : ℕ) : ℚ) := by
    rw [← hcast]; field_simp
  rw [hgeom] at hbern
  have hmdiv : (1 : ℚ) ≤ (m : ℚ) * (1 / ((m - 1 : ℕ) : ℚ)) := by
    rw [mul_one_div, le_div_iff₀ hm1]; linarith
  have hratio : (2 : ℚ) ≤ ((m : ℚ) / ((m - 1 : ℕ) : ℚ)) ^ m := by linarith
  have hmul := mul_le_mul_of_nonneg_right hratio (le_of_lt (pow_pos hm1 m))
  have hcancel : ((m : ℚ) / ((m - 1 : ℕ) : ℚ)) ^ m * ((m - 1 : ℕ) : ℚ) ^ m = (m : ℚ) ^ m := by
    rw [div_pow]; exact div_mul_cancel₀ _ (pow_ne_zero m (ne_of_gt hm1))
  rw [hcancel] at hmul
  have h2 : (2 : ℚ) * ((m - 1 : ℕ) : ℚ) ^ m ≤ (m : ℚ) ^ m := by
    calc (2 : ℚ) * ((m - 1 : ℕ) : ℚ) ^ m = (((m - 1 : ℕ) : ℚ) ^ m) * 2 := by ring
    _ ≤ (m : ℚ) ^ m := by linarith
  rw [div_pow, div_le_iff₀ (pow_pos hm0 m)]
  linarith
