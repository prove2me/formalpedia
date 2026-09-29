-- Prove2me | solution 1 for WorkbookSource.base_51926
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:16.893041+00:00
-- url     : https://prove2.me/submissions/9ade7390-1188-4fd8-b447-4761b0256972

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c k : ℝ): a^2 + b^2 + c^2 + k*a + k^2 / 3 ≥ a * b + b * c + c * a + k * c  := by
  have h0 : 0 ≤ (1 : ℝ) * (-a/2 - b/2 + c - k/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (3/4 : ℝ) * (-a + b - k/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (a b c k : ℝ), a^2 + b^2 + c^2 + k*a + k^2 / 3 ≥ a * b + b * c + c * a + k * c) := @solution
#print axioms solution
