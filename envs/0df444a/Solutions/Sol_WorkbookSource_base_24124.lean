-- Prove2me | solution 1 for WorkbookSource.base_24124
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:47:40.234348+00:00
-- url     : https://prove2.me/submissions/fa65cad0-a4d3-4f4a-821d-69ab48c1ae64

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : 2 * (a ^ 4 + b ^ 4 + c ^ 4) + a * b * c * (a + b + c) ≥ 3 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a)  := by
  have h0 : 0 ≤ (2 : ℝ) * (-5*a^2/16 + 3*a*b/8 - 3*a*c/4 - 5*b^2/16 + c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (231/128 : ℝ) * (-5*a^2/11 + 10*a*b/77 + 12*a*c/77 + b^2 - 64*b*c/77)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (63/44 : ℝ) * (a^2 - 17*a*b/21 - 5*a*c/21 + b*c/21)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ), 2 * (a ^ 4 + b ^ 4 + c ^ 4) + a * b * c * (a + b + c) ≥ 3 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a)) := @solution
#print axioms solution
