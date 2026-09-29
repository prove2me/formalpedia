-- Prove2me | solution 1 for WorkbookSource.base_46897
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:26.746329+00:00
-- url     : https://prove2.me/submissions/f8f637fa-5de9-4ac9-856c-166ea5174d70

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : 9 * (a ^ 3 * (b + c) + b ^ 3 * (c + a) + c ^ 3 * (a + b)) + 3 * (a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b) ≤ 4 * (a ^ 4 + b ^ 4 + c ^ 4) + 17 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)  := by
  have h0 : 0 ≤ (12 : ℝ) * (-a*b/8 - a*c/8 - 3*b^2/8 + b*c - 3*c^2/8)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (189/16 : ℝ) * (-8*a^2/21 - a*b/7 + a*c - b^2/21 - 3*c^2/7)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (81/7 : ℝ) * (-4*a^2/9 + a*b - 4*b^2/9 - c^2/9)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ), 9 * (a ^ 3 * (b + c) + b ^ 3 * (c + a) + c ^ 3 * (a + b)) + 3 * (a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b) ≤ 4 * (a ^ 4 + b ^ 4 + c ^ 4) + 17 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)) := @solution
#print axioms solution
