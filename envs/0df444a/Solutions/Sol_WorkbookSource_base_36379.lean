-- Prove2me | solution 1 for WorkbookSource.base_36379
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:12.225197+00:00
-- url     : https://prove2.me/submissions/ec8a5c55-853e-4ebc-bac9-787fc70f5bb2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c d : ℝ) : 2 * (a + b + c + d) ^ 4 + (a * b + b * c + c * d + d * a + a * c + b * d) ^ 2 ≥ 3 * a * b * c * d + 289 / 96 * (a + b + c + d) ^ 2 * (a * b + b * c + c * d + d * a + a * c + b * d)  := by
  have h0 : 0 ≤ (437/96 : ℝ) * (188*a^2/437 + 238*a*b/437 + 675*a*c/874 + 675*a*d/874 + 188*b^2/437 + 675*b*c/874 + 675*b*d/874 + 479*c^2/874 + c*d + 479*d^2/874)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (44775/13984 : ℝ) * (2663*a^2/5970 + a*b + a*c/2 + a*d/2 + 2663*b^2/5970 + b*c/2 + b*d/2 + 559*c^2/2985 + 559*d^2/2985)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (199/192 : ℝ) * (-103*a^2/398 - a*c + 103*b^2/398 + b*d - 103*c^2/398 + 103*d^2/398)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (199/192 : ℝ) * (-103*a^2/398 - a*d + 103*b^2/398 + b*c + 103*c^2/398 - 103*d^2/398)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (1215/3184 : ℝ) * (-a^2/3 - b^2/3 - c^2/3 + d^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (135/398 : ℝ) * (-a^2/2 - b^2/2 + c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h6 : 0 ≤ (405/1592 : ℝ) * (-a^2 + b^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5, h6]
example : (∀ (a b c d : ℝ), 2 * (a + b + c + d) ^ 4 + (a * b + b * c + c * d + d * a + a * c + b * d) ^ 2 ≥ 3 * a * b * c * d + 289 / 96 * (a + b + c + d) ^ 2 * (a * b + b * c + c * d + d * a + a * c + b * d)) := @solution
#print axioms solution
