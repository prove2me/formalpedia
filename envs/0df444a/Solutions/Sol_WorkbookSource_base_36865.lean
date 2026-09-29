-- Prove2me | solution 1 for WorkbookSource.base_36865
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:14.002084+00:00
-- url     : https://prove2.me/submissions/3ae5005a-0e2e-41ef-9b99-5d60b1358c02

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b : ℝ) : 4 * a * b * (a^2 - b^2) ≤ (a^2 + b^2)^2  := by
  have h0 : 0 ≤ (4 : ℝ) * (-a^2/2 + a*b + b^2/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0]
example : (∀ (a b : ℝ), 4 * a * b * (a^2 - b^2) ≤ (a^2 + b^2)^2) := @solution
#print axioms solution
