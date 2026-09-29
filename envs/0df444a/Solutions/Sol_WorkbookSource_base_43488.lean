-- Prove2me | solution 1 for WorkbookSource.base_43488
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:22.347674+00:00
-- url     : https://prove2.me/submissions/2cc14564-4a40-4239-b063-5ffe8b1d9fec

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) + 8 * a * b * c ≥ (a + b + c + a * b * c) * (1 + a * b + b * c + c * a)  := by
  have h0 : 0 ≤ (1 : ℝ) * (a*b*c/2 - a/2 - b/2 - c/2 + 1)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (1 : ℝ) * (-a*b*c/2 + a/2 + b*c - b/2 - c/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (1 : ℝ) * (-a*b*c/2 + a*c - a/2 + b/2 - c/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (1 : ℝ) * (-a*b*c/2 + a*b - a/2 - b/2 + c/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3]
example : (∀ (a b c : ℝ), (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) + 8 * a * b * c ≥ (a + b + c + a * b * c) * (1 + a * b + b * c + c * a)) := @solution
#print axioms solution
