-- Prove2me | solution 1 for WorkbookSource.base_30799
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:08.864893+00:00
-- url     : https://prove2.me/submissions/b8c337e0-9a9a-45cd-a2da-ceca7beb3812

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : 2 * x ^ 2 * (3 * x + y) ^ 2 + 2 * y ^ 2 * (3 * y + z) ^ 2 - (3 * x + y) ^ 2 * y * (2 * y + z + x) ≥ 0  := by
  have h0 : 0 ≤ (18 : ℝ) * (x^2 + x*y/12 - 5*y^2/6 - y*z/4)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (63/8 : ℝ) * (x*y - 2*y^2/3 - y*z/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (x y z : ℝ), 2 * x ^ 2 * (3 * x + y) ^ 2 + 2 * y ^ 2 * (3 * y + z) ^ 2 - (3 * x + y) ^ 2 * y * (2 * y + z + x) ≥ 0) := @solution
#print axioms solution
