-- Prove2me | solution 1 for WorkbookSource.base_13717
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:44:38.298735+00:00
-- url     : https://prove2.me/submissions/3b229e88-43eb-435a-9a5b-d514ef49eab1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : 2 * (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) ≥ (a + 1) * (b + 1) * (c + 1) * (a + b + c - 1) + 2 * (a * b * c - 1) ^ 2  := by
  have h0 : 0 ≤ (2 : ℝ) * (-a*b/4 - a*c/4 + a/10 + b*c - b/4 - c/4 - 1/10)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (15/8 : ℝ) * (-a*b/3 + a*c - 6*a/25 + b/5 - c/3 - 22/75)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (5/3 : ℝ) * (a*b - 9*a/25 - 3*b/10 - c/50 - 8/25)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (333/500 : ℝ) * (-56*a/333 - 155*b/333 + c - 122/333)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (26522/41625 : ℝ) * (a - 6080*b/13261 - 7181/13261)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (4930/13261 : ℝ) * (1 - b)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (a b c : ℝ), 2 * (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) ≥ (a + 1) * (b + 1) * (c + 1) * (a + b + c - 1) + 2 * (a * b * c - 1) ^ 2) := @solution
#print axioms solution
