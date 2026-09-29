-- Prove2me | solution 1 for WorkbookSource.plus_56211
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:39.537645+00:00
-- url     : https://prove2.me/submissions/fc991656-a651-4262-bc2f-5131ecf523b9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : 8 * (b ^ 2 + c ^ 2 + a ^ 2) ^ 2 + 27 * (a + b + c) * a * b * c ≥ 9 * (a * b + b * c + c * a) * (b ^ 2 + c ^ 2 + a ^ 2) + 3 * (a + b + c) * (a + b) * (b + c) * (c + a)   := by
  have h0 : 0 ≤ (18 : ℝ) * (2*a^2/3 - a*b/2 - a*c/2 - b^2/3 + b*c - c^2/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (27/2 : ℝ) * (-a*b + a*c + 2*b^2/3 - 2*c^2/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (a b c : ℝ), 8 * (b ^ 2 + c ^ 2 + a ^ 2) ^ 2 + 27 * (a + b + c) * a * b * c ≥ 9 * (a * b + b * c + c * a) * (b ^ 2 + c ^ 2 + a ^ 2) + 3 * (a + b + c) * (a + b) * (b + c) * (c + a)) := @solution
#print axioms solution
