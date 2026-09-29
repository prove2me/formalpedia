-- Prove2me | solution 1 for WorkbookSource.base_52535
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:17.632621+00:00
-- url     : https://prove2.me/submissions/cae063c1-2839-43f4-b458-fb0af8e69633

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c d : ℝ) : (17 / 8) * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 - 4 * a * b * c * d) ≥ (a + b + c + d) * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 - a * b * c - a * b * d - a * c * d - b * c * d)  := by
  have h0 : 0 ≤ (9/8 : ℝ) * (-a^2/3 + 4*a*b/9 + 4*a*c/9 - 4*a*d/9 - b^2/3 + 4*b*c/9 - 4*b*d/9 - c^2/3 - 4*c*d/9 + d^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (1 : ℝ) * (-a^2/2 + 2*a*b/3 - a*c/3 + a*d/3 - b^2/2 - b*c/3 + b*d/3 + c^2 - 2*c*d/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (3/4 : ℝ) * (-a^2 + 2*a*c/3 + 2*a*d/3 + b^2 - 2*b*c/3 - 2*b*d/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (1/12 : ℝ) * (-a*b + c*d)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (1/12 : ℝ) * (-a*c + b*d)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (1/12 : ℝ) * (-a*d + b*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (a b c d : ℝ), (17 / 8) * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 - 4 * a * b * c * d) ≥ (a + b + c + d) * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 - a * b * c - a * b * d - a * c * d - b * c * d)) := @solution
#print axioms solution
