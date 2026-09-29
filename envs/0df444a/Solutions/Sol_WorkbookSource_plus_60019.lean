-- Prove2me | solution 1 for WorkbookSource.plus_60019
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:40.338527+00:00
-- url     : https://prove2.me/submissions/0e561271-4274-4b39-90ad-b41786eca20c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) :
  (a^2 + b^2 + c^2) * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) + 6 * a * b * c * (a + b) * (b + c) * (c + a) ≥ 7 * a^2 * b^2 * c^2   := by
  have h0 : 0 ≤ (8 : ℝ) * (a^2*b/4 + a^2*c/4 + a*b^2/4 + a*b*c + a*c^2/4 + b^2*c/4 + b*c^2/4)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (1/2 : ℝ) * (-a^2*b + a^2*c + a*b^2 - a*c^2 - b^2*c + b*c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (a b c : ℝ), (a^2 + b^2 + c^2) * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) + 6 * a * b * c * (a + b) * (b + c) * (c + a) ≥ 7 * a^2 * b^2 * c^2) := @solution
#print axioms solution
