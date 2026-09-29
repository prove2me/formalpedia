-- Prove2me | solution 1 for WorkbookSource.base_18619
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:04:15.532997+00:00
-- url     : https://prove2.me/submissions/098b1b7a-a3e3-4a67-96a3-84721a82aa8f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2)^2 + 3 * (a^3 * b + b^3 * c + c^3 * a) ≥ 6 * a * b * c * (a + b + c)  := by
  have h0 : 0 ≤ (3 : ℝ) * (1) * (-a^2/2 - a*b/2 - a*c/2 + b^2/2 + b*c)^2 := by positivity
  have h1 : 0 ≤ (9/4 : ℝ) * (1) * (-a^2/3 - a*b + a*c - b^2/3 + 2*c^2/3)^2 := by positivity
  nlinarith only [h0, h1]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b^2 + c^2)^2 + 3 * (a^3 * b + b^3 * c + c^3 * a) ≥ 6 * a * b * c * (a + b + c)) := @solution
#print axioms solution
