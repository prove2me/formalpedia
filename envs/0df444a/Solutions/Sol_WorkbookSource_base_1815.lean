-- Prove2me | solution 1 for WorkbookSource.base_1815
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:58.296986+00:00
-- url     : https://prove2.me/submissions/98eb76bb-cdf2-473e-8f8f-a1733cf61949

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) :
  (a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (c^2 + c * a + a^2) ≥ (a * b + b * c + c * a)^3 + (1/6) * (a - b)^2 * (a - c)^2 * (b - c)^2  := by
  have h0 : 0 ≤ (2 : ℝ) * (-a^2*b/6 - a^2*c/6 - a*b^2/6 + a*b*c - a*c^2/6 - b^2*c/6 - b*c^2/6)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (7/9 : ℝ) * (-13*a^2*b/14 - a^2*c/2 - a*b^2/2 + 11*a*c^2/14 + b^2*c/7 + b*c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (16/21 : ℝ) * (-3*a^2*b/8 - 7*a^2*c/8 + 7*a*b^2/8 - 5*a*c^2/8 + b^2*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ), (a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (c^2 + c * a + a^2) ≥ (a * b + b * c + c * a)^3 + (1/6) * (a - b)^2 * (a - c)^2 * (b - c)^2) := @solution
#print axioms solution
