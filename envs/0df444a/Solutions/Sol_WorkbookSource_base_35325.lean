-- Prove2me | solution 1 for WorkbookSource.base_35325
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:09.96538+00:00
-- url     : https://prove2.me/submissions/a8dcd548-7a0e-4715-97d7-64bcfcd1722a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c d : ℝ) : (a * b + b * c + c * d + d * a + a * c + b * d) ^ 2 ≥ (9 / 4) * (a + b + c + d) * (a * b * c + b * c * d + c * d * a + d * a * b)  := by
  have h0 : 0 ≤ (1 : ℝ) * (-a*b/2 - a*c/8 - a*d/8 - b*c/8 - b*d/8 + c*d)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (63/64 : ℝ) * (-4*a*b/21 - 11*a*c/21 - a*d/7 - b*c/7 + b*d)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (27/28 : ℝ) * (-2*a*b/9 - 2*a*c/9 - 5*a*d/9 + b*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (2/3 : ℝ) * (-a*b/2 - a*c/2 + a*d)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (1/2 : ℝ) * (-a*b + a*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4]
example : (∀ (a b c d : ℝ), (a * b + b * c + c * d + d * a + a * c + b * d) ^ 2 ≥ (9 / 4) * (a + b + c + d) * (a * b * c + b * c * d + c * d * a + d * a * b)) := @solution
#print axioms solution
