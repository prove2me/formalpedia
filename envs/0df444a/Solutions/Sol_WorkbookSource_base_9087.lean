-- Prove2me | solution 1 for WorkbookSource.base_9087
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:44:31.712267+00:00
-- url     : https://prove2.me/submissions/19217446-c3a5-4e18-b1fe-bba2bc012900

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : (a^2+b^2+c^2-2*a*b-2*b*c-2*c*a)^2 + 9*(a*b+b*c+c*a)^2 ≥ 30*a*b*c*(a+b+c)  := by
  have h0 : 0 ≤ (16 : ℝ) * (a^2/4 - a*b/2 - a*c/2 - b^2/8 + b*c - c^2/8)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (12 : ℝ) * (-a*b + a*c + b^2/4 - c^2/4)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (a b c : ℝ), (a^2+b^2+c^2-2*a*b-2*b*c-2*c*a)^2 + 9*(a*b+b*c+c*a)^2 ≥ 30*a*b*c*(a+b+c)) := @solution
#print axioms solution
