-- Prove2me | solution 1 for WorkbookSource.base_28276
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:05.260017+00:00
-- url     : https://prove2.me/submissions/27e8bfbf-06b2-4a50-8219-0448dc2b361b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : (a^2 + 1/2) * (b^2 + 1/2) * (c^2 + 1/2) ≥ (a + b - 1/2) * (b + c - 1/2) * (c + a - 1/2)  := by
  have h0 : 0 ≤ (1 : ℝ) * (a*b*c - a/3 - b/3 - c/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (23/36 : ℝ) * (-12*a*b/23 - 18*a*c/23 + 17*a/23 - 18*b*c/23 + 17*b/23 + c - 9/23)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (15/46 : ℝ) * (a*b + 2*a*c/9 - 7*a/9 + 2*b*c/9 - 7*b/9 + 1/9)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (4/27 : ℝ) * (-a*c/4 - a/4 - b*c/4 - b/4 + 1)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (1/12 : ℝ) * (a*c - a - b*c + b)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4]
example : (∀ (a b c : ℝ), (a^2 + 1/2) * (b^2 + 1/2) * (c^2 + 1/2) ≥ (a + b - 1/2) * (b + c - 1/2) * (c + a - 1/2)) := @solution
#print axioms solution
