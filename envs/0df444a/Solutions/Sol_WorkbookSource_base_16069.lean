-- Prove2me | solution 1 for WorkbookSource.base_16069
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:04:13.673564+00:00
-- url     : https://prove2.me/submissions/1973ec41-c918-4a8b-b23a-ec4d712f7ab0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3 + 9 * a * b * c) * (a + b + c) ≥ 4 * (a * b + b * c + c * a)^2  := by
  have h0 : 0 ≤ (1 : ℝ) * (1) * (-a^2/2 + a*b - a*c/2 - b^2/2 - b*c/2 + c^2)^2 := by positivity
  have h1 : 0 ≤ (3/4 : ℝ) * (1) * (a^2 - a*c - b^2 + b*c)^2 := by positivity
  have h2 : 0 ≤ (2 : ℝ) * (b*c) * (-b + c)^2 := by positivity
  have h3 : 0 ≤ (2 : ℝ) * (a*c) * (-a + c)^2 := by positivity
  have h4 : 0 ≤ (2 : ℝ) * (a*b) * (-a + b)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 + b^3 + c^3 + 9 * a * b * c) * (a + b + c) ≥ 4 * (a * b + b * c + c * a)^2) := @solution
#print axioms solution
