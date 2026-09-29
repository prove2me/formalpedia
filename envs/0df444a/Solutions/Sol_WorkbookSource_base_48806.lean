-- Prove2me | solution 1 for WorkbookSource.base_48806
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:28.164794+00:00
-- url     : https://prove2.me/submissions/29839cde-6639-4e1d-adac-57775203eb31

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : a^4+b^4+c^4+4*a+4*b+4*c+12 ≥ 3*a^2+3*b^2+3*c^2+2*a*b^2+2*b*c^2+2*c*a^2  := by
  have h0 : 0 ≤ (12 : ℝ) * (-a^2/6 + a/6 - b^2/6 + b/6 - c^2/6 + c/6 + 1)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (2/3 : ℝ) * (-a^2 - a/2 + b^2/2 - b/2 + c^2/2 + c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (1/2 : ℝ) * (a - b^2 - b + c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ), a^4+b^4+c^4+4*a+4*b+4*c+12 ≥ 3*a^2+3*b^2+3*c^2+2*a*b^2+2*b*c^2+2*c*a^2) := @solution
#print axioms solution
