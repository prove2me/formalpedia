-- Prove2me | solution 1 for WorkbookSource.base_3684
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:40:54.258037+00:00
-- url     : https://prove2.me/submissions/bee544e2-ef8b-4e9a-b123-549c70b2b87d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : (x + y) ^ 2 + 13 * (x ^ 2 + y ^ 2) + 14 * z ^ 2 - 2 * x * y ≥ x ^ 2 + 4 * x * y + 4 * y ^ 2 + 9 * z ^ 2 + 6 * x * z + 12 * y * z  := by
  have h0 : 0 ≤ (13 : ℝ) * (x - 2*y/13 - 3*z/13)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (126/13 : ℝ) * (y - 2*z/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (x y z : ℝ), (x + y) ^ 2 + 13 * (x ^ 2 + y ^ 2) + 14 * z ^ 2 - 2 * x * y ≥ x ^ 2 + 4 * x * y + 4 * y ^ 2 + 9 * z ^ 2 + 6 * x * z + 12 * y * z) := @solution
#print axioms solution
