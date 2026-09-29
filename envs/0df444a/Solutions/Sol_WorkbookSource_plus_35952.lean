-- Prove2me | solution 1 for WorkbookSource.plus_35952
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:23.94961+00:00
-- url     : https://prove2.me/submissions/9fafa554-4cd5-446f-82b0-dc3624e825ca

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c d : ℝ) : (a * c + b * d) ^ 2 + (3 / 4) * (a ^ 2 + c ^ 2 + b ^ 2 + d ^ 2) ^ 2 ≥ (a + b + c + d) * (a * b ^ 2 + b * c ^ 2 + c * d ^ 2 + a ^ 2 * d)   := by
  have h0 : 0 ≤ (1 : ℝ) * (-a^2/3 - a*b/2 - a*c/3 + a*d/2 + b*c/2 + b*d - c^2/3 - c*d/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (8/9 : ℝ) * (-a^2/8 + 3*a*b/8 + a*c - 3*a*d/8 - 3*b^2/8 - 3*b*c/8 - c^2/8 + 3*c*d/8 - 3*d^2/8)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (5/8 : ℝ) * (-a^2/5 - 3*a*b/5 - a*d/5 + b^2 - b*c/5 - c^2/5 - 3*c*d/5 + d^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (3/5 : ℝ) * (a^2 - a*b/3 - 2*a*d/3 - 2*b*c/3 + c^2 - c*d/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3]
example : (∀ (a b c d : ℝ), (a * c + b * d) ^ 2 + (3 / 4) * (a ^ 2 + c ^ 2 + b ^ 2 + d ^ 2) ^ 2 ≥ (a + b + c + d) * (a * b ^ 2 + b * c ^ 2 + c * d ^ 2 + a ^ 2 * d)) := @solution
#print axioms solution
