-- Prove2me | solution 1 for WorkbookSource.base_11517
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:44:37.5233+00:00
-- url     : https://prove2.me/submissions/d3cb2dda-9adc-4e88-9c3d-b978e0f05fe1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution {a b c : ℝ} : (a + b + c + 2 * (a * b + b * c + c * a)) ^ 2 ≤ 9 * (a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2))  := by
  have h0 : 0 ≤ (14 : ℝ) * (-2*a*b/7 - 2*a*c/7 - a/7 + b*c - b/7 - c/7)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (90/7 : ℝ) * (-2*a*b/5 + a*c - a/5 - b/5 - c/5)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (54/5 : ℝ) * (a*b - a/3 - b/3 - c/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (6 : ℝ) * (-a/2 - b/2 + c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (9/2 : ℝ) * (-a + b)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4]
example : (∀ {a b c : ℝ}, (a + b + c + 2 * (a * b + b * c + c * a)) ^ 2 ≤ 9 * (a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2))) := @solution
#print axioms solution
