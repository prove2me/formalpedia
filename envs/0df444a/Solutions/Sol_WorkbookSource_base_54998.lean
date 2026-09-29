-- Prove2me | solution 1 for WorkbookSource.base_54998
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:32.646713+00:00
-- url     : https://prove2.me/submissions/574c8223-c832-4653-ad8b-c5bcdb1a4e8c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b : ℝ) : 12 * a ^ 2 + 36 * a * b + 36 * b ^ 2 + 7 ≥ 18 * a + 24 * b  := by
  have h0 : 0 ≤ (36 : ℝ) * (a/2 + b - 1/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (3 : ℝ) * (1 - a)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (a b : ℝ), 12 * a ^ 2 + 36 * a * b + 36 * b ^ 2 + 7 ≥ 18 * a + 24 * b) := @solution
#print axioms solution
