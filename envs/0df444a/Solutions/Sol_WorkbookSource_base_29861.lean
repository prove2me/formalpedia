-- Prove2me | solution 1 for WorkbookSource.base_29861
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:55:45.400382+00:00
-- url     : https://prove2.me/submissions/4a7bde00-4d23-4be1-8b3c-d43125eed324

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * a ^ 2 + b * c) * (2 * b ^ 2 + a * c) * (2 * c ^ 2 + a * b) ≥ (a * b + b * c + c * a) ^ 3  := by
  have h0 : 0 ≤ (3 : ℝ) * (b*c) * (-a^2/6 - 5*a*b/12 - 5*a*c/12 + b*c)^2 := by positivity
  have h1 : 0 ≤ (23/12 : ℝ) * (b*c) * (a^2 - a*b/2 - a*c/2)^2 := by positivity
  have h2 : 0 ≤ (3 : ℝ) * (a*c) * (-5*a*b/12 + a*c - b^2/6 - 5*b*c/12)^2 := by positivity
  have h3 : 0 ≤ (23/12 : ℝ) * (a*c) * (-a*b/2 + b^2 - b*c/2)^2 := by positivity
  have h4 : 0 ≤ (3 : ℝ) * (a*b) * (a*b - 5*a*c/12 - 5*b*c/12 - c^2/6)^2 := by positivity
  have h5 : 0 ≤ (23/12 : ℝ) * (a*b) * (-a*c/2 - b*c/2 + c^2)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (2 * a ^ 2 + b * c) * (2 * b ^ 2 + a * c) * (2 * c ^ 2 + a * b) ≥ (a * b + b * c + c * a) ^ 3) := @solution
#print axioms solution
