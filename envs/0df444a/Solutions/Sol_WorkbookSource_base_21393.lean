-- Prove2me | solution 1 for WorkbookSource.base_21393
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:55:39.966482+00:00
-- url     : https://prove2.me/submissions/e03883a2-8078-4402-8029-0c246a6f8736

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x^3 * y + x * y^3 + 1 ≥ x^2 * y + x * y^2 + x * y  := by
  have h0 : 0 ≤ (1 : ℝ) * (1) * (-x*y + 1)^2 := by positivity
  have h1 : 0 ≤ (1 : ℝ) * (x*y) * (-x/2 - y/2 + 1)^2 := by positivity
  have h2 : 0 ≤ (3/4 : ℝ) * (x*y) * (-x + y)^2 := by positivity
  nlinarith only [h0, h1, h2]
example : (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), x^3 * y + x * y^3 + 1 ≥ x^2 * y + x * y^2 + x * y) := @solution
#print axioms solution
