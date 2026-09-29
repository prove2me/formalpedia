-- Prove2me | solution 1 for WorkbookSource.base_33547
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:09.135576+00:00
-- url     : https://prove2.me/submissions/bfed9000-a3b1-45b8-beec-35e24ee573b5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : (a^4 + b^4 + c^4 + 5 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)) / 2 ≥ 3 * a * b * c * (a + b + c)  := by
  have h0 : 0 ≤ (21/10 : ℝ) * (-3*a^2/7 - 2*a*b/7 - 2*a*c/7 + b*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (27/14 : ℝ) * (-2*a^2/15 - 2*a*b/5 + a*c - 7*b^2/15)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (81/50 : ℝ) * (-2*a^2/9 + a*b - 2*b^2/9 - 5*c^2/9)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ), (a^4 + b^4 + c^4 + 5 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)) / 2 ≥ 3 * a * b * c * (a + b + c)) := @solution
#print axioms solution
