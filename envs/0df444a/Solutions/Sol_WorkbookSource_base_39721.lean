-- Prove2me | solution 1 for WorkbookSource.base_39721
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:19.428722+00:00
-- url     : https://prove2.me/submissions/9510dfd1-7c65-444d-968b-4501d2b775b6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) :
  2 * (x + y + z) ^ 4 ≥ 9 * (x * y + y * z + z * x) * (x ^ 2 + y ^ 2 + z ^ 2 + x * y + y * z + z * x)  := by
  have h0 : 0 ≤ (2 : ℝ) * (x^2/4 - x*y - x*z/4 + y^2/4 - y*z/4 + z^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (15/8 : ℝ) * (-x^2 + x*z/5 - y^2/5 + y*z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (9/5 : ℝ) * (-x*z + y^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (x y z : ℝ), 2 * (x + y + z) ^ 4 ≥ 9 * (x * y + y * z + z * x) * (x ^ 2 + y ^ 2 + z ^ 2 + x * y + y * z + z * x)) := @solution
#print axioms solution
