-- Prove2me | solution 1 for WorkbookSource.base_5143
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:40:57.991875+00:00
-- url     : https://prove2.me/submissions/d95f8c3c-8316-404d-93ad-b8dd553b9353

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a c : ℝ) : 3 * (a ^ 2 - a + 1) * (c ^ 2 - c + 1) ≥ 2 * (a ^ 2 * c ^ 2 - a * c + 1)  := by
  have h0 : 0 ≤ (3 : ℝ) * (-a*c/2 + a/2 + c - 1/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (9/4 : ℝ) * (-a*c/3 + a - 1/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (a c : ℝ), 3 * (a ^ 2 - a + 1) * (c ^ 2 - c + 1) ≥ 2 * (a ^ 2 * c ^ 2 - a * c + 1)) := @solution
#print axioms solution
