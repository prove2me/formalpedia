-- Prove2me | solution 1 for WorkbookSource.plus_76073
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:44.038052+00:00
-- url     : https://prove2.me/submissions/935e36d0-58df-4418-a8c6-fa6dab4c3bca

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : a^2 * b^2 * c^2 + 2 * a^2 * b^2 + 2 * b^2 * c^2 + 2 * c^2 * a^2 + a^2 + b^2 + c^2 ≥ (a * b * c - 1) * (a * b + b * c + c * a)   := by
  have h0 : 0 ≤ (2 : ℝ) * (-a*b*c/4 - a/16 + b*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (2 : ℝ) * (-a*b*c/4 + a*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (2 : ℝ) * (-a*b*c/4 + a*b + c/16)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (1 : ℝ) * (a/2 + b + c/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (95/128 : ℝ) * (4*a*b*c/95 + 32*a/95 + c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (8001/12160 : ℝ) * (-4*a*b*c/63 + a)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h6 : 0 ≤ (313/504 : ℝ) * (a*b*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5, h6]
example : (∀ (a b c : ℝ), a^2 * b^2 * c^2 + 2 * a^2 * b^2 + 2 * b^2 * c^2 + 2 * c^2 * a^2 + a^2 + b^2 + c^2 ≥ (a * b * c - 1) * (a * b + b * c + c * a)) := @solution
#print axioms solution
