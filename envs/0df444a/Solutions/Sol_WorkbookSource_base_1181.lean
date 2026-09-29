-- Prove2me | solution 1 for WorkbookSource.base_1181
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:40:48.947389+00:00
-- url     : https://prove2.me/submissions/3e6c7016-9985-4456-9aed-2f9ad719965e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : a^4 + b^4 + c^4 + 17 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) ≥ 6 * (a + b + c) * (a^2 * b + b^2 * c + c^2 * a)  := by
  have h0 : 0 ≤ (12 : ℝ) * (a^2/4 - a*b/2 - a*c/2 - b^2/4 + b*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (9 : ℝ) * (a^2/6 - a*b + a*c + b^2/6 - c^2/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (a b c : ℝ), a^4 + b^4 + c^4 + 17 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) ≥ 6 * (a + b + c) * (a^2 * b + b^2 * c + c^2 * a)) := @solution
#print axioms solution
