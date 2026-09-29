-- Prove2me | solution 1 for WorkbookSource.base_38173
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:17.044283+00:00
-- url     : https://prove2.me/submissions/0b8b55e8-2a3e-438d-8e01-8c0ba52b432f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : (4 * (a - b) ^ 2 * (-c + b) ^ 2 * (c - a) ^ 2 + 3 * (b ^ 2 * c ^ 2 * (a - b) * (a - c) + c ^ 2 * a ^ 2 * (b - a) * (b - c) + a ^ 2 * b ^ 2 * (c - a) * (c - b)) + 3 * a * b * c * (a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b))) ≥ 0  := by
  have h0 : 0 ≤ (4 : ℝ) * (-a^2*b/4 + a^2*c/4 + a*b^2/4 - 5*a*c^2/8 - 5*b^2*c/8 + b*c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (15/4 : ℝ) * (-3*a^2*b/5 + a^2*c/5 + a*b^2 - a*c^2/10 - b^2*c/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (18/5 : ℝ) * (-a^2*b/2 + a^2*c - a*c^2/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (3/2 : ℝ) * (-a^2*b/2 - a*c^2/2 + b^2*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (9/8 : ℝ) * (-a^2*b + a*c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4]
example : (∀ (a b c : ℝ), (4 * (a - b) ^ 2 * (-c + b) ^ 2 * (c - a) ^ 2 + 3 * (b ^ 2 * c ^ 2 * (a - b) * (a - c) + c ^ 2 * a ^ 2 * (b - a) * (b - c) + a ^ 2 * b ^ 2 * (c - a) * (c - b)) + 3 * a * b * c * (a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b))) ≥ 0) := @solution
#print axioms solution
