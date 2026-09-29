-- Prove2me | solution 1 for WorkbookSource.plus_14687
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:21.293977+00:00
-- url     : https://prove2.me/submissions/225e77d4-ed64-4aa0-ab75-2478b7589e90

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : a^4 + b^4 + c^4 + (11/2)*(a * b + b * c + c * a)^2 + 3 * (a * b^3 + b * c^3 + c * a^3) + 4 * (a^3 * b + b^3 * c + c^3 * a) ≥ 0   := by
  have h0 : 0 ≤ (9/2 : ℝ) * (a^2/3 + 8*a*b/9 + 8*a*c/9 + 4*b^2/9 + b*c + c^2/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (17/18 : ℝ) * (3*a^2/17 + 8*a*b/17 + a*c - 5*b^2/17 + 12*c^2/17)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (25/34 : ℝ) * (4*a^2/5 + a*b - b^2/5 - c^2/5)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ), a^4 + b^4 + c^4 + (11/2)*(a * b + b * c + c * a)^2 + 3 * (a * b^3 + b * c^3 + c * a^3) + 4 * (a^3 * b + b^3 * c + c^3 * a) ≥ 0) := @solution
#print axioms solution
