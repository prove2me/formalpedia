-- Prove2me | solution 1 for WorkbookSource.base_18478
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:17:01.290338+00:00
-- url     : https://prove2.me/submissions/684bd3c7-35d4-4aad-9e5f-f35004ee6753

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) :
  3 * (a^4 + b^4 + c^4) - (a^3 + b^3 + c^3) ≥ (a^3 + b^3 + c^3) - (1/3) * (a^2 + b^2 + c^2)  := by
  have h0 : 0 ≤ (3 : ℝ) * (c^2 - c/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (3 : ℝ) * (b^2 - b/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (3 : ℝ) * (a^2 - a/3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ), 3 * (a^4 + b^4 + c^4) - (a^3 + b^3 + c^3) ≥ (a^3 + b^3 + c^3) - (1/3) * (a^2 + b^2 + c^2)) := @solution
#print axioms solution
