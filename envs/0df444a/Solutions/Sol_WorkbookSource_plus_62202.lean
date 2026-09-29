-- Prove2me | solution 1 for WorkbookSource.plus_62202
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:26.330413+00:00
-- url     : https://prove2.me/submissions/07d8b1af-ee75-49fc-8113-7d6be413246e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c d : ℝ) : a^4 + b^4 + c^4 + d^4 + 2 * (a - b) * (b - c) * (c - d) * (d - a) ≥ 4 * a * b * c * d   := by
  have h0 : 0 ≤ (1 : ℝ) * (-a^2/2 - a*b/2 + a*c/2 + b^2/2 - b*c/2 - c^2/2 + d^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (1 : ℝ) * (-a^2/2 - a*c/2 + a*d/2 - b^2/2 + b*c/2 - b*d/2 + c*d)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (3/4 : ℝ) * (a^2/3 - a*b + a*c/3 - 2*a*d/3 - b^2/3 - b*c/3 + 2*b*d/3 + c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (5/12 : ℝ) * (a^2/5 - a*c + a*d/5 - b^2/5 - b*c/5 + b*d)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (2/5 : ℝ) * (-a^2 - a*d + b^2 + b*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4]
example : (∀ (a b c d : ℝ), a^4 + b^4 + c^4 + d^4 + 2 * (a - b) * (b - c) * (c - d) * (d - a) ≥ 4 * a * b * c * d) := @solution
#print axioms solution
