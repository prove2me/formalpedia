-- Prove2me | solution 1 for WorkbookSource.base_56863
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:03:31.79598+00:00
-- url     : https://prove2.me/submissions/cba84ecd-f152-4ac8-8ccb-9cb2eb787c29

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) * (a + b) * (b + c) * (c + a) ≥ (a^3 + b^3 + c^3 + 5 * a * b * c) * (a * b + b * c + c * a)  := by
  have h0 : 0 ≤ (3 : ℝ) * (c) * (a*b - a*c/2 - b*c/2)^2 := by positivity
  have h1 : 0 ≤ (1/4 : ℝ) * (c) * (-a*c + b*c)^2 := by positivity
  have h2 : 0 ≤ (3 : ℝ) * (b) * (-a*b/2 + a*c - b*c/2)^2 := by positivity
  have h3 : 0 ≤ (1/4 : ℝ) * (b) * (-a*b + b*c)^2 := by positivity
  have h4 : 0 ≤ (3 : ℝ) * (a) * (-a*b/2 - a*c/2 + b*c)^2 := by positivity
  have h5 : 0 ≤ (1/4 : ℝ) * (a) * (-a*b + a*c)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b^2 + c^2) * (a + b) * (b + c) * (c + a) ≥ (a^3 + b^3 + c^3 + 5 * a * b * c) * (a * b + b * c + c * a)) := @solution
#print axioms solution
