-- Prove2me | solution 1 for WorkbookSource.base_36056
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:55:47.744919+00:00
-- url     : https://prove2.me/submissions/e42af39d-b982-4b6e-9523-14ed7e5c9156

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 * b + b^3 * c + c^3 * a + 4 * (a * b^3 + b * c^3 + c * a^3) ≥ 4 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) + a * b * c * (a + b + c)  := by
  have h0 : 0 ≤ (4 : ℝ) * (b*c) * (-a/2 - b/2 + c)^2 := by positivity
  have h1 : 0 ≤ (4 : ℝ) * (a*c) * (a - b/2 - c/2)^2 := by positivity
  have h2 : 0 ≤ (4 : ℝ) * (a*b) * (-a/2 + b - c/2)^2 := by positivity
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a^3 * b + b^3 * c + c^3 * a + 4 * (a * b^3 + b * c^3 + c * a^3) ≥ 4 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) + a * b * c * (a + b + c)) := @solution
#print axioms solution
