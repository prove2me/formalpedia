-- Prove2me | solution 1 for WorkbookSource.base_21519
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:47:39.42476+00:00
-- url     : https://prove2.me/submissions/a7112d33-1124-4132-9bde-b84d19a487d5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : (a - b) ^ 4 * (b - c) ^ 2 + (b - c) ^ 4 * (c - a) ^ 2 + (c - a) ^ 4 * (a - b) ^ 2 ≥ 5 * (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2  := by
  have h0 : 0 ≤ (36 : ℝ) * (a^3/6 - a^2*b/6 - a^2*c/3 - a*b^2/3 + a*b*c - a*c^2/6 + b^3/6 - b^2*c/6 - b*c^2/3 + c^3/6)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0]
example : (∀ (a b c : ℝ), (a - b) ^ 4 * (b - c) ^ 2 + (b - c) ^ 4 * (c - a) ^ 2 + (c - a) ^ 4 * (a - b) ^ 2 ≥ 5 * (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2) := @solution
#print axioms solution
