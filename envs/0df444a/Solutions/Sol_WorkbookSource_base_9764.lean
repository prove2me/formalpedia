-- Prove2me | solution 1 for WorkbookSource.base_9764
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:44:32.907107+00:00
-- url     : https://prove2.me/submissions/c2c5573a-ec27-4841-b9f8-22d826f64058

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : (x + y + z) ^ 4 ≥ 9 * (x ^ 3 * y + 2 * x ^ 2 * y * z + y ^ 3 * z + 2 * y ^ 2 * z * x + z ^ 3 * x + 2 * z ^ 2 * x * y)  := by
  have h0 : 0 ≤ (7 : ℝ) * (x^2/14 - x*y/2 - x*z/2 - 5*y^2/14 + y*z + 2*z^2/7)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (21/4 : ℝ) * (3*x^2/7 - x*y + x*z - y^2/7 - 2*z^2/7)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (x y z : ℝ), (x + y + z) ^ 4 ≥ 9 * (x ^ 3 * y + 2 * x ^ 2 * y * z + y ^ 3 * z + 2 * y ^ 2 * z * x + z ^ 3 * x + 2 * z ^ 2 * x * y)) := @solution
#print axioms solution
