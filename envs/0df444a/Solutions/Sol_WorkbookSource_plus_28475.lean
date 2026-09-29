-- Prove2me | solution 1 for WorkbookSource.plus_28475
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:22.213802+00:00
-- url     : https://prove2.me/submissions/adaa3c9b-b8e1-47d4-ab0e-cd8b96f9f45f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : (a^2 + 2) * (b^2 + 2) * (c^2 + 2) ≥ 3 / 2 * (a * b + b * c + c * a)^2   := by
  have h0 : 0 ≤ (8 : ℝ) * (-a*b/12 - a*c/12 - b*c/12 + 1)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (4 : ℝ) * (-a*b*c/3 + a/6 + b/6 + c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (35/9 : ℝ) * (-2*a*b*c/7 + a/7 + b)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (80/21 : ℝ) * (-a*b*c/4 + a)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (4/9 : ℝ) * (-a*b/2 - a*c/2 + b*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (1/3 : ℝ) * (-a*b + a*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (a b c : ℝ), (a^2 + 2) * (b^2 + 2) * (c^2 + 2) ≥ 3 / 2 * (a * b + b * c + c * a)^2) := @solution
#print axioms solution
