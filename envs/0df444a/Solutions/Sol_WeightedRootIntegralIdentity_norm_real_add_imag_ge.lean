-- Prove2me | solution 1 for WeightedRootIntegralIdentity.norm_real_add_imag_ge
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T08:47:25.360889+00:00
-- url     : https://prove2.me/submissions/f3695654-e25c-4641-800e-16e898f161c4

import Mathlib

theorem solution (x ε : ℝ) (hx : 0 ≤ x) :
    x ≤ ‖(x : ℂ) + ε * Complex.I‖ := by
  have h := Complex.re_le_norm ((x : ℂ) + ε * Complex.I)
  simpa using h
