-- Prove2me | solution 1 for WorkbookSource.base_21127
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:44:42.760409+00:00
-- url     : https://prove2.me/submissions/12b96736-f3ed-4c58-9801-69c56f211f04

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : 13 * (a ^ 4 + b ^ 4 + c ^ 4) + (a + b + c) ^ 4 ≥ 20 * (a ^ 3 * b + a ^ 3 * c + b ^ 3 * c + b ^ 3 * a + c ^ 3 * a + c ^ 3 * b)  := by
  have h0 : 0 ≤ (14 : ℝ) * (-2*a^2/7 + 5*a*b/7 - 4*a*c/7 - 2*b^2/7 - 4*b*c/7 + c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (90/7 : ℝ) * (-2*a^2/5 - 2*a*b/5 + 3*a*c/5 + b^2 - 4*b*c/5)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (54/5 : ℝ) * (a^2 - 2*a*b/3 - 2*a*c/3 + b*c/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ), 13 * (a ^ 4 + b ^ 4 + c ^ 4) + (a + b + c) ^ 4 ≥ 20 * (a ^ 3 * b + a ^ 3 * c + b ^ 3 * c + b ^ 3 * a + c ^ 3 * a + c ^ 3 * b)) := @solution
#print axioms solution
