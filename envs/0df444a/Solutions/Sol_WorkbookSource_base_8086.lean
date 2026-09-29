-- Prove2me | solution 1 for WorkbookSource.base_8086
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:41:03.074293+00:00
-- url     : https://prove2.me/submissions/9be7d5ce-b4d4-4645-89eb-4bbb8e65b317

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : (a^2 + 2) * (b^2 + 2) * (c^2 + 2) ≥ (a + b + c)^2 + (a * b + b * c + c * a)^2  := by
  have h0 : 0 ≤ (8 : ℝ) * (-a*b/80 - a*c/80 + 1)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (3 : ℝ) * (-a*b*c/6 - 3*a/10 - b/3 + c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (273/100 : ℝ) * (-635*a*b*c/2457 + a - 40*b/91)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (584/273 : ℝ) * (-100*a*b*c/219 + b)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (1 : ℝ) * (-a*b/2 - a*c/2 + b*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (599/800 : ℝ) * (-5009*a*b/5391 + a*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h6 : 0 ≤ (5114/17739 : ℝ) * (a*b*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h7 : 0 ≤ (4966/48519 : ℝ) * (a*b)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7]
example : (∀ (a b c : ℝ), (a^2 + 2) * (b^2 + 2) * (c^2 + 2) ≥ (a + b + c)^2 + (a * b + b * c + c * a)^2) := @solution
#print axioms solution
