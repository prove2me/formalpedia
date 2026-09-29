-- Prove2me | solution 1 for WorkbookSource.base_81
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:40:47.293135+00:00
-- url     : https://prove2.me/submissions/b5d2ee01-ec4d-40f5-abb8-e6eca9298cb1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + 3 * (a^2 + b^2 + c^2) + 6 ≥ 2 * (a + b + c) + 4 * (a * b + b * c + c * a)  := by
  have h0 : 0 ≤ (6 : ℝ) * (-a*b/6 - a*c/6 - a/6 - b*c/6 - b/6 - c/6 + 1)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (17/6 : ℝ) * (-a*b/17 - a*c/17 - 7*a/17 - b*c/17 - 7*b/17 + c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (40/17 : ℝ) * (-a*b/10 - a*c/10 - 7*a/10 - b*c/10 + b)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (6/5 : ℝ) * (-a*b/3 - a*c/3 + a - b*c/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (2/3 : ℝ) * (-a*b/2 - a*c/2 + b*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (1/2 : ℝ) * (-a*b + a*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (a b c : ℝ), a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + 3 * (a^2 + b^2 + c^2) + 6 ≥ 2 * (a + b + c) + 4 * (a * b + b * c + c * a)) := @solution
#print axioms solution
