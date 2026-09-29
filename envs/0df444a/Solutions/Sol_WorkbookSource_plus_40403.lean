-- Prove2me | solution 1 for WorkbookSource.plus_40403
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:24.705299+00:00
-- url     : https://prove2.me/submissions/d4c83190-dc82-40b4-824f-f9da4d422bcc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : a ^ 4 + b ^ 4 + c ^ 4 + a ^ 3 * b + b ^ 3 * c + c ^ 3 * a ≥ (3 / 5) * (a * b + b * c + c * a) ^ 2   := by
  have h0 : 0 ≤ (1 : ℝ) * (-7*a^2/15 - 16*a*b/35 + a*c/2 - 7*b^2/15 + c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (176/225 : ℝ) * (-7*a^2/8 - 3*a*b/11 - 705*a*c/2464 + b^2 + 225*b*c/352)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (11/60 : ℝ) * (a^2 + 6*a*b/11 + 9*a*c/44 - 3*b*c/28)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (94/8085 : ℝ) * (273*a*b/752 + 273*a*c/752 + b*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (98195/9727872 : ℝ) * (273*a*b/1025 + a*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (28261/3013500 : ℝ) * (a*b)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (a b c : ℝ), a ^ 4 + b ^ 4 + c ^ 4 + a ^ 3 * b + b ^ 3 * c + c ^ 3 * a ≥ (3 / 5) * (a * b + b * c + c * a) ^ 2) := @solution
#print axioms solution
