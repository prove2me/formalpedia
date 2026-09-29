-- Prove2me | solution 1 for WorkbookSource.plus_74167
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:43.342093+00:00
-- url     : https://prove2.me/submissions/d04c52fb-55e0-49d3-8b36-b17d71f581fc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : 4 * z ^ 6 + x ^ 6 + y ^ 6 + 3 * x ^ 2 * y ^ 2 * (x ^ 2 + y ^ 2) ≥ 4 * (x ^ 3 * y ^ 3 + y ^ 3 * z ^ 3 + z ^ 3 * x ^ 3)   := by
  have h0 : 0 ≤ (4 : ℝ) * (-x^3/2 - y^3/2 + z^3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (3 : ℝ) * (-x^2*y + x*y^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (x y z : ℝ), 4 * z ^ 6 + x ^ 6 + y ^ 6 + 3 * x ^ 2 * y ^ 2 * (x ^ 2 + y ^ 2) ≥ 4 * (x ^ 3 * y ^ 3 + y ^ 3 * z ^ 3 + z ^ 3 * x ^ 3)) := @solution
#print axioms solution
