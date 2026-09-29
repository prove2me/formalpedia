-- Prove2me | solution 1 for WorkbookSource.base_54170
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:29.61974+00:00
-- url     : https://prove2.me/submissions/67740cb0-1c7a-4ae1-9f84-0d2a804354c4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : 2 * (x * y + y * z + z * x) * (x ^ 2 + y ^ 2 + z ^ 2) ≤ 11 * x * y * z * (x + y + z) + 4 * (x ^ 4 + y ^ 4 + z ^ 4)  := by
  have h0 : 0 ≤ (4 : ℝ) * (-x^2/2 + x*y/2 - x*z/4 - y^2/2 - y*z/4 + z^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (15/4 : ℝ) * (2*x^2/5 + 4*x*y/5 + 3*x*z/5 - 2*y^2/5 + y*z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (12/5 : ℝ) * (-x^2 + x*y/2 + x*z + y^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (x y z : ℝ), 2 * (x * y + y * z + z * x) * (x ^ 2 + y ^ 2 + z ^ 2) ≤ 11 * x * y * z * (x + y + z) + 4 * (x ^ 4 + y ^ 4 + z ^ 4)) := @solution
#print axioms solution
