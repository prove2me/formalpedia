-- Prove2me | solution 1 for WorkbookSource.plus_48956
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:25.519258+00:00
-- url     : https://prove2.me/submissions/685f0243-e297-4402-a112-73d9be39f14e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c d : ℝ) : 5 * (a * b + b * c + c * d + d * a + a * c + b * d) ^ 2 ≥ 7 / 2 * a * b * c * d + 65 / 32 * (a + b + c + d) * (a * c * d + b * c * d + b * a * c + a * b * d)   := by
  have h0 : 0 ≤ (5 : ℝ) * (239*a*b/400 + 51*a*c/64 + 51*a*d/64 + 51*b*c/64 + 51*b*d/64 + c*d)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (102879/32000 : ℝ) * (a*b + 425*a*c/852 + 425*a*d/852 + 425*b*c/852 + 425*b*d/852)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (9315/9088 : ℝ) * (-39761*a*c/46575 + 17*a*d/1863 + 17*b*c/1863 + b*d)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (15275/14904 : ℝ) * (1292*a*c/76375 - 65213*a*d/76375 + b*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (106039/381875 : ℝ) * (646*a*c/5581 + a*d)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (191121/697625 : ℝ) * (a*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (a b c d : ℝ), 5 * (a * b + b * c + c * d + d * a + a * c + b * d) ^ 2 ≥ 7 / 2 * a * b * c * d + 65 / 32 * (a + b + c + d) * (a * c * d + b * c * d + b * a * c + a * b * d)) := @solution
#print axioms solution
