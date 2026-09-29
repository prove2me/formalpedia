-- Prove2me | solution 1 for WorkbookSource.plus_9631
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:34.072014+00:00
-- url     : https://prove2.me/submissions/44676ce7-1c26-41ee-a5ad-f602780e00bd

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : 352 * (a ^ 4 + b ^ 4 + c ^ 4) - 536 * (a ^ 3 * (b + c) + b ^ 3 * (c + a) + c ^ 3 * (a + b)) + 411 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + 336 * (a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b) ≥ 0   := by
  have h0 : 0 ≤ (571 : ℝ) * (272*a^2/571 - 104*a*b/571 - 104*a*c/571 - 268*b^2/571 + b*c - 268*c^2/571)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (315225/571 : ℝ) * (-924*a^2/2335 - 104*a*b/467 + a*c + 944*b^2/2335 - 268*c^2/467)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (245025/467 : ℝ) * (-28*a^2/55 + a*b - 28*b^2/55 + 16*c^2/55)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ), 352 * (a ^ 4 + b ^ 4 + c ^ 4) - 536 * (a ^ 3 * (b + c) + b ^ 3 * (c + a) + c ^ 3 * (a + b)) + 411 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + 336 * (a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b) ≥ 0) := @solution
#print axioms solution
