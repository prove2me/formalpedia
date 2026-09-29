-- Prove2me | solution 1 for WorkbookSource.base_15043
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:44:39.637135+00:00
-- url     : https://prove2.me/submissions/031aaeb6-2fb4-47a9-9bf7-a1039a7c7331

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (r_a r_b r_c : ℝ) : 3 * r_a * r_b + r_b * r_c + r_c * r_a ≤ (r_a + r_b + r_c) ^ 2  := by
  have h0 : 0 ≤ (1 : ℝ) * (r_a/2 + r_b/2 + r_c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (3/4 : ℝ) * (-r_a + r_b)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (r_a r_b r_c : ℝ), 3 * r_a * r_b + r_b * r_c + r_c * r_a ≤ (r_a + r_b + r_c) ^ 2) := @solution
#print axioms solution
