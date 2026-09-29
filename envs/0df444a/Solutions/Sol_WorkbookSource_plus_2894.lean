-- Prove2me | solution 1 for WorkbookSource.plus_2894
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:33.241141+00:00
-- url     : https://prove2.me/submissions/f00098fc-4c3f-4295-bfc4-be4d7e2d44df

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : 4 * ((a - b) * (a - c) * (a ^ 2 - b ^ 2) * (a ^ 2 - c ^ 2) + (b - c) * (b - a) * (b ^ 2 - c ^ 2) * (b ^ 2 - a ^ 2) + (c - a) * (c - b) * (c ^ 2 - a ^ 2) * (c ^ 2 - b ^ 2)) + (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 ≥ 0   := by
  have h0 : 0 ≤ (4 : ℝ) * (a^3 - a^2*b/2 - a^2*c/2 - a*b^2/2 - a*c^2/2 + b^3 - b^2*c/2 - b*c^2/2 + c^3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0]
example : (∀ (a b c : ℝ), 4 * ((a - b) * (a - c) * (a ^ 2 - b ^ 2) * (a ^ 2 - c ^ 2) + (b - c) * (b - a) * (b ^ 2 - c ^ 2) * (b ^ 2 - a ^ 2) + (c - a) * (c - b) * (c ^ 2 - a ^ 2) * (c ^ 2 - b ^ 2)) + (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 ≥ 0) := @solution
#print axioms solution
