-- Prove2me | solution 1 for WorkbookSource.base_374
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:04:07.586591+00:00
-- url     : https://prove2.me/submissions/db9cca28-b48b-446f-84bd-cfc8435dc852

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 * b + b^2 * c + c^2 * a) * (a * b^2 + b * c^2 + c * a^2) ≥ 9 * a^2 * b^2 * c^2  := by
  have h0 : 0 ≤ (1 : ℝ) * (b*c) * (-a^2 + b*c)^2 := by positivity
  have h1 : 0 ≤ (1 : ℝ) * (a*c) * (-a*c + b^2)^2 := by positivity
  have h2 : 0 ≤ (1 : ℝ) * (a*b) * (-a*b + c^2)^2 := by positivity
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 * b + b^2 * c + c^2 * a) * (a * b^2 + b * c^2 + c * a^2) ≥ 9 * a^2 * b^2 * c^2) := @solution
#print axioms solution
