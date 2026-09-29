-- Prove2me | solution 1 for WorkbookSource.base_1076
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:57.596679+00:00
-- url     : https://prove2.me/submissions/2e9b13ae-b40d-4493-bf9f-911617670e14

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c d : ℝ) : (a^2+b^2+c^2+d^2)^2+16*a*b*c*d ≥ 2*(a+c)^2*(b+d)^2  := by
  have h0 : 0 ≤ (2 : ℝ) * (a*b - a*d - b*c + c*d)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (1 : ℝ) * (-a^2 + b^2 - c^2 + d^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (a b c d : ℝ), (a^2+b^2+c^2+d^2)^2+16*a*b*c*d ≥ 2*(a+c)^2*(b+d)^2) := @solution
#print axioms solution
