-- Prove2me | solution 1 for WorkbookSource.base_11191
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:44:36.573023+00:00
-- url     : https://prove2.me/submissions/695d283f-cd8e-4e30-8745-e79b46ac4536

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) :
  (a^2 + b^2) * (a - b)^2 + (b^2 + c^2) * (b - c)^2 + (c^2 + a^2) * (c - a)^2 + 2 * a * b * c * (a + b + c) ≥ 0  := by
  have h0 : 0 ≤ (2 : ℝ) * (a^2/9 - a*b/18 - a*c/2 + b^2/9 - b*c/2 + c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (160/81 : ℝ) * (a^2/10 - a*b/2 + b^2 - 9*b*c/20)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (88/45 : ℝ) * (a^2 - 5*a*b/11 - 5*a*c/11 + b*c/22)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (43/66 : ℝ) * (a*b + a*c + b*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3]
example : (∀ (a b c : ℝ), (a^2 + b^2) * (a - b)^2 + (b^2 + c^2) * (b - c)^2 + (c^2 + a^2) * (c - a)^2 + 2 * a * b * c * (a + b + c) ≥ 0) := @solution
#print axioms solution
