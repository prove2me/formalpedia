-- Prove2me | solution 1 for WorkbookSource.base_46341
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:15.287711+00:00
-- url     : https://prove2.me/submissions/e3807f40-cc32-4ba6-bccb-bd99dd2289ca

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c d : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ d * (a + b + c)  := by
  have h0 : 0 ≤ (1 : ℝ) * (-a/2 - b/2 - c/2 + d)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (3/4 : ℝ) * (-a/3 - b/3 + c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (2/3 : ℝ) * (-a/2 + b)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (1/2 : ℝ) * (a)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3]
example : (∀ (a b c d : ℝ), a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ d * (a + b + c)) := @solution
#print axioms solution
