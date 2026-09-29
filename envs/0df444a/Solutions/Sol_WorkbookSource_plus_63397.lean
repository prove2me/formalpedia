-- Prove2me | solution 1 for WorkbookSource.plus_63397
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:41.883066+00:00
-- url     : https://prove2.me/submissions/9b1ff21a-8fb5-46a5-8cb7-b5596fd6eff4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : (a^4 + a^2 * b * c) * (a - b) * (a - c) + (b^4 + b^2 * c * a) * (b - c) * (b - a) + (c^4 + c^2 * a * b) * (c - a) * (c - b) ≥ 0   := by
  have h0 : 0 ≤ (2 : ℝ) * (a^3/3 - a^2*b/3 - a^2*c/3 - a*b^2/3 + a*b*c - a*c^2/3 + b^3/3 - b^2*c/3 - b*c^2/3 + c^3/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (7/9 : ℝ) * (-a^3/2 + a^2*b/2 - a^2*c/7 + a*b^2/2 - 5*a*c^2/14 - b^3/2 - b^2*c/7 - 5*b*c^2/14 + c^3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (7/12 : ℝ) * (-a^3 + a^2*b/7 + 4*a^2*c/7 - a*b^2/7 + 3*a*c^2/7 + b^3 - 4*b^2*c/7 - 3*b*c^2/7)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (5/21 : ℝ) * (a^2*b/2 - a^2*c/2 - a*b^2/2 + a*c^2/2 - b^2*c + b*c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (5/28 : ℝ) * (-a^2*b - a^2*c + a*b^2 + a*c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4]
example : (∀ (a b c : ℝ), (a^4 + a^2 * b * c) * (a - b) * (a - c) + (b^4 + b^2 * c * a) * (b - c) * (b - a) + (c^4 + c^2 * a * b) * (c - a) * (c - b) ≥ 0) := @solution
#print axioms solution
