-- Prove2me | solution 1 for WorkbookSource.base_35723
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:10.660622+00:00
-- url     : https://prove2.me/submissions/01f15cd1-2fc6-41d8-bf80-6e88a59285a5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y : ℝ) : x * y * (x ^ 2 + y ^ 2) ≤ 2 + 1 / 2 * (x + y - 2) * (x + y) ^ 3  := by
  have h0 : 0 ≤ (2 : ℝ) * (-x^2/4 - x*y/2 - y^2/4 + 1)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (3/2 : ℝ) * (x^2/6 + x*y - 2*x/3 + y^2/6 - 2*y/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (1/3 : ℝ) * (-x^2 + x - y^2 + y)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (x y : ℝ), x * y * (x ^ 2 + y ^ 2) ≤ 2 + 1 / 2 * (x + y - 2) * (x + y) ^ 3) := @solution
#print axioms solution
