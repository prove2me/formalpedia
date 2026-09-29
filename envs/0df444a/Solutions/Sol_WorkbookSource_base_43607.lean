-- Prove2me | solution 1 for WorkbookSource.base_43607
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:14.555636+00:00
-- url     : https://prove2.me/submissions/70983456-c57c-40a3-bbef-0cdb8e5737a3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : 3 * (x ^ 2 + x * y + y ^ 2) * (y ^ 2 + y * z + z ^ 2) * (z ^ 2 + z * x + x ^ 2) ≥ 9 / 4 * (y + z) ^ 2 * (x ^ 2 + (y + z) * x / 2 + y * z) ^ 2  := by
  have h0 : 0 ≤ (39/16 : ℝ) * (-2*x^2*y/13 + 2*x^2*z/13 - x*y^2 + x*z^2 - 2*y^2*z/13 + 2*y*z^2/13)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (9/13 : ℝ) * (5*x^2*y/8 - 5*x^2*z/8 - y^2*z + y*z^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (27/64 : ℝ) * (-x^2*y + x^2*z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (x y z : ℝ), 3 * (x ^ 2 + x * y + y ^ 2) * (y ^ 2 + y * z + z ^ 2) * (z ^ 2 + z * x + x ^ 2) ≥ 9 / 4 * (y + z) ^ 2 * (x ^ 2 + (y + z) * x / 2 + y * z) ^ 2) := @solution
#print axioms solution
