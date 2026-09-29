-- Prove2me | solution 1 for WorkbookSource.base_969
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:57.022538+00:00
-- url     : https://prove2.me/submissions/7e83a532-b662-462e-8fb8-77b2264234b5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : (x + y + z) ^ 2 + 6 * x * y * z + (x * y + x * z + y * z) ^ 2 ≥ (2 / 3) * (x * y + x * z + y * z) * (2 * x + 3 + 2 * y + 2 * z) + 2 * (x + y + z) * x * y * z  := by
  have h0 : 0 ≤ (1 : ℝ) * (x*y/3 - 2*x*z/3 - 2*y*z/3 + z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (1 : ℝ) * (-2*x*y/3 + x*z/3 - 2*y*z/3 + y)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (1 : ℝ) * (-2*x*y/3 - 2*x*z/3 + x + y*z/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (x y z : ℝ), (x + y + z) ^ 2 + 6 * x * y * z + (x * y + x * z + y * z) ^ 2 ≥ (2 / 3) * (x * y + x * z + y * z) * (2 * x + 3 + 2 * y + 2 * z) + 2 * (x + y + z) * x * y * z) := @solution
#print axioms solution
