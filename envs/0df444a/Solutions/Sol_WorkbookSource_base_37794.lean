-- Prove2me | solution 1 for WorkbookSource.base_37794
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:16.243205+00:00
-- url     : https://prove2.me/submissions/8bd3a95f-3fd5-47e6-b185-e09004f351cc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : (a^2+b^2+c^2)^3 ≥ (a^3+b^3+c^3)^2  := by
  have h0 : 0 ≤ (3 : ℝ) * (a^2*b/3 - b^2*c/3 + b*c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (3 : ℝ) * (-a^2*c/3 + a*b^2/3 + a*c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (8/3 : ℝ) * (a^2*b/8 + 3*a^2*c/8 + b^2*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (8/3 : ℝ) * (-3*a^2*b/8 + a^2*c/8 + a*b^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (9/4 : ℝ) * (a^2*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (9/4 : ℝ) * (a^2*b)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (a b c : ℝ), (a^2+b^2+c^2)^3 ≥ (a^3+b^3+c^3)^2) := @solution
#print axioms solution
