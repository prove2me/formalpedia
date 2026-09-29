-- Prove2me | solution 1 for WorkbookSource.base_11043
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:44:35.748963+00:00
-- url     : https://prove2.me/submissions/5c434633-512b-42d7-a48f-c860eec6b5a2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y : ℝ) : (x * y + 2) ^ 2 + (x - 1) ^ 2 + (y - 1) ^ 2 ≥ 4  := by
  have h0 : 0 ≤ (2 : ℝ) * (x*y/2 - x/2 - y/2 + 1)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (1/2 : ℝ) * (x*y + x + y)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (x y : ℝ), (x * y + 2) ^ 2 + (x - 1) ^ 2 + (y - 1) ^ 2 ≥ 4) := @solution
#print axioms solution
