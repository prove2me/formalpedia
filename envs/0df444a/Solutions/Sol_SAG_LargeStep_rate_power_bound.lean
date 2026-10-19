-- Prove2me | solution 1 for SAG.LargeStep.rate_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T19:26:40.458483+00:00
-- url     : https://prove2.me/submissions/a7c8a6e9-0784-4b5d-83b1-055ba10c848d

import Mathlib

set_option autoImplicit false

theorem solution (n : ℕ) (hn : 0 < n) :
    (1 - 1 / (8 * (n : ℝ))) ^ (-(n : ℤ)) ≤ 8 / 7 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : 0 < 1 - 1 / (8 * (n : ℝ)) := by
    have : 1 / (8 * (n : ℝ)) ≤ 1 / 8 := by
      apply one_div_le_one_div_of_le (by norm_num)
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    linarith
  have bern : 1 + (n : ℝ) * (-(1 / (8 * (n : ℝ)))) ≤ (1 + -(1 / (8 * (n : ℝ)))) ^ n := by
    apply one_add_mul_le_pow
    have : 0 ≤ 1 / (8 * (n : ℝ)) := by positivity
    linarith
  have e1 : 1 + (n : ℝ) * (-(1 / (8 * (n : ℝ)))) = 7 / 8 := by
    field_simp; ring
  rw [e1] at bern
  have e2 : (1 : ℝ) + -(1 / (8 * (n : ℝ))) = 1 - 1 / (8 * (n : ℝ)) := by ring
  rw [e2] at bern
  rw [zpow_neg, zpow_natCast]
  have hp : 0 < (1 - 1 / (8 * (n : ℝ))) ^ n := pow_pos hb n
  rw [inv_le_comm₀ hp (by norm_num)]
  linarith
