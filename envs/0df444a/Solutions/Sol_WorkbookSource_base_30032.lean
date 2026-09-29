-- Prove2me | solution 1 for WorkbookSource.base_30032
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:07.014818+00:00
-- url     : https://prove2.me/submissions/1304c734-447a-4a20-b2c2-117485f290e7

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : (a^2 + b * a + b^2) * (b^2 + c * b + c^2) * (c^2 + a * c + a^2) ≥ a * b * c * (a + b + c)^3  := by
  have h0 : 0 ≤ (1 : ℝ) * (-a^2*b/2 - a^2*c/2 - a*b^2/2 + b^2*c/2 + b*c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (1 : ℝ) * (-a^2*b/2 + a^2*c/2 - a*b^2/2 + a*c^2 - b^2*c/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (1/2 : ℝ) * (-a^2*b + b^2*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (1/2 : ℝ) * (-a^2*c + a*b^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3]
example : (∀ (a b c : ℝ), (a^2 + b * a + b^2) * (b^2 + c * b + c^2) * (c^2 + a * c + a^2) ≥ a * b * c * (a + b + c)^3) := @solution
#print axioms solution
