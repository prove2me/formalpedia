-- Prove2me | solution 1 for WorkbookSource.base_5070
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:40:57.252839+00:00
-- url     : https://prove2.me/submissions/5836418a-0b90-491b-a8c4-83472b22e85e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x : ℝ) : 4 * x^4 - 7 * x + 4 > 0  := by
  have h0 : 0 ≤ (2078/479 : ℝ) * (x - 3353/4156)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (4 : ℝ) * (x^2 - 1039/1916)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (19/1907113592 : ℝ) * (1)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (x : ℝ), 4 * x^4 - 7 * x + 4 > 0) := @solution
#print axioms solution
