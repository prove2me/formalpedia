-- Prove2me | solution 1 for WorkbookSource.base_31356
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:07.636511+00:00
-- url     : https://prove2.me/submissions/2e4a6ae6-be40-41e7-a5e5-4014a4df511c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c d : ℝ) : 2 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) ≥ 2 * (a ^ 2 * c ^ 2 + b ^ 2 * d ^ 2 + a * b * d ^ 2 + a * b * c ^ 2)  := by
  have h0 : 0 ≤ (2 : ℝ) * (-a*b/2 - b^2/2 + d^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (2 : ℝ) * (-a^2/2 - a*b/2 + c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (3/2 : ℝ) * (-2*a^2/3 - a*b/3 + b^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (5/6 : ℝ) * (-a^2 + a*b)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3]
example : (∀ (a b c d : ℝ), 2 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) ≥ 2 * (a ^ 2 * c ^ 2 + b ^ 2 * d ^ 2 + a * b * d ^ 2 + a * b * c ^ 2)) := @solution
#print axioms solution
