-- Prove2me | solution 1 for PassivityUn.symm_antisymm_dim
-- status  : ACCEPTED   (prove)
-- author  : @ShapeZero
-- created : 2026-09-23T21:35:35.367155+00:00
-- url     : https://prove2.me/submissions/d775d537-2ab0-4454-a0e4-6be33de86eb3

import Mathlib

theorem solution (n : ℕ) :
    n * (n + 1) / 2 + n * (n - 1) / 2 = n ^ 2 := by
  rcases n with _ | k
  · simp
  · have h2 : 2 ∣ (k + 1) * k := by
      rw [mul_comm]; exact even_iff_two_dvd.mp (Nat.even_mul_succ_self k)
    simp only [Nat.add_sub_cancel]
    rw [← Nat.add_div_of_dvd_left h2]
    have : (k + 1) * (k + 1 + 1) + (k + 1) * k = 2 * (k + 1) ^ 2 := by ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
