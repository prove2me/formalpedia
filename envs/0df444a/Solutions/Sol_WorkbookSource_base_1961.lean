-- Prove2me | solution 1 for WorkbookSource.base_1961
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:40:51.730568+00:00
-- url     : https://prove2.me/submissions/94c62ede-6dd8-4ee1-bcaf-6ee6e84ba949

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : a^4+b^4+c^4+(a+b+c)^4 ≥ 28*a*b*c*(a+b+c)  := by
  have h0 : 0 ≤ (8 : ℝ) * (-a^2/2 - a*b/2 - a*c/2 + b^2/4 + b*c + c^2/4)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (6 : ℝ) * (-a*b + a*c - b^2/2 + c^2/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (a b c : ℝ), a^4+b^4+c^4+(a+b+c)^4 ≥ 28*a*b*c*(a+b+c)) := @solution
#print axioms solution
