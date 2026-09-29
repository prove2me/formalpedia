-- Prove2me | solution 1 for WorkbookSource.base_33453
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:10.319976+00:00
-- url     : https://prove2.me/submissions/11c07439-15dc-4285-9efe-0c85f176daba

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : (x ^ 2 + y ^ 2 + z ^ 2) ^ 3 ≥ (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 + (x * y ^ 2 + y * z ^ 2 + z * x ^ 2) ^ 2 + (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) ^ 2  := by
  have h0 : 0 ≤ (2 : ℝ) * (x^2*y/2 - x^2*z/2 - x*y^2/2 - y^2*z/2 + y*z^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (2 : ℝ) * (-x^2*y/2 - x^2*z/2 + x*y^2/2 + x*z^2 - y^2*z/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (1 : ℝ) * (-x^2*y + y^2*z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (1 : ℝ) * (-x^2*z + x*y^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3]
example : (∀ (x y z : ℝ), (x ^ 2 + y ^ 2 + z ^ 2) ^ 3 ≥ (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 + (x * y ^ 2 + y * z ^ 2 + z * x ^ 2) ^ 2 + (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) ^ 2) := @solution
#print axioms solution
