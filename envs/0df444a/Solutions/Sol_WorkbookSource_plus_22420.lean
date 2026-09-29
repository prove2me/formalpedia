-- Prove2me | solution 1 for WorkbookSource.plus_22420
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:42.916985+00:00
-- url     : https://prove2.me/submissions/f12093ad-3142-474c-b98b-8f947c0b4b92

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^4 * b + a^4 * c + b^4 * c + b^4 * a + c^4 * a + c^4 * b + 2 * a * b * c * (a * b + b * c + c * a) ≥ a^3 * b^2 + a^3 * c^2 + b^3 * c^2 + b^3 * a^2 + c^3 * a^2 + c^3 * b^2 + 2 * a * b * c * (a^2 + b^2 + c^2)   := by
  have h0 : 0 ≤ (1 : ℝ) * (c) * (a^2 - a*c - b^2 + b*c)^2 := by positivity
  have h1 : 0 ≤ (1 : ℝ) * (b) * (-a^2 + a*b - b*c + c^2)^2 := by positivity
  have h2 : 0 ≤ (1 : ℝ) * (a) * (a*b - a*c - b^2 + c^2)^2 := by positivity
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a^4 * b + a^4 * c + b^4 * c + b^4 * a + c^4 * a + c^4 * b + 2 * a * b * c * (a * b + b * c + c * a) ≥ a^3 * b^2 + a^3 * c^2 + b^3 * c^2 + b^3 * a^2 + c^3 * a^2 + c^3 * b^2 + 2 * a * b * c * (a^2 + b^2 + c^2)) := @solution
#print axioms solution
