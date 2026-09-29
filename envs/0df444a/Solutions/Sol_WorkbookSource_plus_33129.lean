-- Prove2me | solution 1 for WorkbookSource.plus_33129
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:23.138131+00:00
-- url     : https://prove2.me/submissions/ca9dd5fe-2faf-4d3c-81e1-d1dc659cc006

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c d : ℝ) : a^4 + b^4 + c^4 + d^4 - 4 * a * b * c * d + (a + b) * (b + c) * (c + d) * (d + a) ≤ (a^2 + b^2 + c^2 + d^2)^2   := by
  have h0 : 0 ≤ (2 : ℝ) * (-a*c/4 - a*d/4 - b*c/4 - b*d/4 + c*d)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (2 : ℝ) * (a*b - a*c/4 - a*d/4 - b*c/4 - b*d/4)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (7/4 : ℝ) * (-3*a*c/7 - a*d/7 + b*c - 3*b*d/7)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (12/7 : ℝ) * (-a*c/2 + a*d - b*d/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3]
example : (∀ (a b c d : ℝ), a^4 + b^4 + c^4 + d^4 - 4 * a * b * c * d + (a + b) * (b + c) * (c + d) * (d + a) ≤ (a^2 + b^2 + c^2 + d^2)^2) := @solution
#print axioms solution
