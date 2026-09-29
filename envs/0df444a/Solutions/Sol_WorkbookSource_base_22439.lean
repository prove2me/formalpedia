-- Prove2me | solution 1 for WorkbookSource.base_22439
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:17:02.679308+00:00
-- url     : https://prove2.me/submissions/0aaef9c5-4e0c-487d-8265-5bd91b03c630

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : a ^ 4 + b ^ 4 + c ^ 4 + (a * b + b * c + c * a) ^ 2 / 3 ≥ 2 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a)  := by
  have h0 : 0 ≤ (4/3 : ℝ) * (3*a^2/4 - a*b/2 - a*c/2 - 3*b^2/4 + b*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (1 : ℝ) * (-a^2/2 + a*b - a*c - b^2/2 + c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (a b c : ℝ), a ^ 4 + b ^ 4 + c ^ 4 + (a * b + b * c + c * a) ^ 2 / 3 ≥ 2 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a)) := @solution
#print axioms solution
