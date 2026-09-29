-- Prove2me | solution 1 for WorkbookSource.base_27971
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:55:42.702044+00:00
-- url     : https://prove2.me/submissions/7f4ca86c-ebf2-4d88-8dcd-93e0bc4d7492

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a + b) ^ 5 ≥ 12 * a * b * (a ^ 3 + b ^ 3)  := by
  have h0 : 0 ≤ (16 : ℝ) * (b) * (-a^2/4 + a*b - b^2/4)^2 := by positivity
  have h1 : 0 ≤ (16 : ℝ) * (a) * (-a^2/4 + a*b - b^2/4)^2 := by positivity
  nlinarith only [h0, h1]
example : (∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b), (a + b) ^ 5 ≥ 12 * a * b * (a ^ 3 + b ^ 3)) := @solution
#print axioms solution
