-- Prove2me | solution 1 for WorkbookSource.base_42134
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:20.971968+00:00
-- url     : https://prove2.me/submissions/8aade72f-241e-40c5-a6b6-a4e8e5b6d3ef

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) :
  (a^2 - b^2)^2 + (b^2 - c^2)^2 + (c^2 - a^2)^2 + 3 * ((a - b)^2 + (b - c)^2 + (c - a)^2) ≥
    6 * (a - b) * (b - c) * (c - a)  := by
  have h0 : 0 ≤ (6 : ℝ) * (-a^2/2 - a/2 + b^2/2 - b/2 + c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (9/2 : ℝ) * (a^2/3 - a + b^2/3 + b - 2*c^2/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (a b c : ℝ), (a^2 - b^2)^2 + (b^2 - c^2)^2 + (c^2 - a^2)^2 + 3 * ((a - b)^2 + (b - c)^2 + (c - a)^2) ≥
    6 * (a - b) * (b - c) * (c - a)) := @solution
#print axioms solution
