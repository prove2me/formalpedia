-- Prove2me | solution 1 for WorkbookSource.base_33889
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:12.419906+00:00
-- url     : https://prove2.me/submissions/f4b8a1b3-3fe6-4df8-9bae-fcca65e9be6f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : 2 * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) ≥ (a - b)^2 * (b - c)^2 * (c - a)^2  := by
  have h0 : 0 ≤ (4 : ℝ) * (-a^2*b/2 - a^2*c/2 - a*b^2/2 + a*b*c - a*c^2/2 - b^2*c/2 - b*c^2/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0]
example : (∀ (a b c : ℝ), 2 * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) ≥ (a - b)^2 * (b - c)^2 * (c - a)^2) := @solution
#print axioms solution
