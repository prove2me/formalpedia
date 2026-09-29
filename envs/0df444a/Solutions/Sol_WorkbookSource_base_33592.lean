-- Prove2me | solution 1 for WorkbookSource.base_33592
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:11.705579+00:00
-- url     : https://prove2.me/submissions/22114ec8-e5f1-442a-85ea-5d8543f4dc43

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2) * (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2) ≥ (a * b + b * c) ^ 3 + (b * c + c * a) ^ 3 + (c * a + a * b) ^ 3  := by
  have h0 : 0 ≤ (3 : ℝ) * (a^2*b/3 - a^2*c/2 - a*b^2/2 - b^2*c/3 + b*c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (3 : ℝ) * (-a^2*b/2 - a^2*c/3 + a*b^2/3 + a*c^2 - b^2*c/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (23/12 : ℝ) * (-a^2*b + b^2*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (23/12 : ℝ) * (-a^2*c + a*b^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3]
example : (∀ (a b c : ℝ), 3 * (a ^ 2 + b ^ 2) * (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2) ≥ (a * b + b * c) ^ 3 + (b * c + c * a) ^ 3 + (c * a + a * b) ^ 3) := @solution
#print axioms solution
