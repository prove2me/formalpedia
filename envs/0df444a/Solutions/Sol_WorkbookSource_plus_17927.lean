-- Prove2me | solution 1 for WorkbookSource.plus_17927
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:34.928388+00:00
-- url     : https://prove2.me/submissions/9e6d0679-b1b1-4663-a8b2-2262e8f00d7d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : (2 * a ^ 2 + b ^ 2 + c ^ 2) * (2 * b ^ 2 + c ^ 2 + a ^ 2) * (2 * c ^ 2 + a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 * (b + c) ^ 2 * (c + a) ^ 2   := by
  have h0 : 0 ≤ (11/4 : ℝ) * (-13*a^3/22 + 4*a^2*b/11 - a^2*c/2 - a*b^2/2 - 4*a*c^2/11 + 13*b^3/22 + b*c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (11/4 : ℝ) * (-13*a^3/22 - a^2*b/2 + 4*a^2*c/11 - 4*a*b^2/11 - a*c^2/2 + b^2*c + 13*c^3/22)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (299/176 : ℝ) * (3*a^3/23 - a^2*b + a*c^2 - 14*b^3/23 + 11*c^3/23)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (299/176 : ℝ) * (3*a^3/23 - a^2*c + a*b^2 + 11*b^3/23 - 14*c^3/23)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (1/46 : ℝ) * (-a^3/2 - b^3/2 + c^3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : 0 ≤ (3/184 : ℝ) * (-a^3 + b^3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (a b c : ℝ), (2 * a ^ 2 + b ^ 2 + c ^ 2) * (2 * b ^ 2 + c ^ 2 + a ^ 2) * (2 * c ^ 2 + a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 * (b + c) ^ 2 * (c + a) ^ 2) := @solution
#print axioms solution
