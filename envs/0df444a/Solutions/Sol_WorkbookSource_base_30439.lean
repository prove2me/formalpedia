-- Prove2me | solution 1 for WorkbookSource.base_30439
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:07.905138+00:00
-- url     : https://prove2.me/submissions/295a4c89-6af2-4f62-b1ce-bb2f2e0dd9b8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : (a^2 + b^2 + c^2)^2 - 3 * a * b * c * (a + b + c) ≥ 3 * (a + b + c) * (a - b) * (b - c) * (c - a)  := by
  have h0 : 0 ≤ (3 : ℝ) * (-a*b/2 - a*c/2 + b^2/2 + b*c - c^2/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (9/4 : ℝ) * (-2*a^2/3 - a*b + a*c + b^2/3 + c^2/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (a b c : ℝ), (a^2 + b^2 + c^2)^2 - 3 * a * b * c * (a + b + c) ≥ 3 * (a + b + c) * (a - b) * (b - c) * (c - a)) := @solution
#print axioms solution
