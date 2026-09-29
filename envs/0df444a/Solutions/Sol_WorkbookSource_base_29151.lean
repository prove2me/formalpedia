-- Prove2me | solution 1 for WorkbookSource.base_29151
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:55:44.679044+00:00
-- url     : https://prove2.me/submissions/80282189-8aee-4d52-a2f3-62f364474051

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :  b * c * (a ^ 3 + a ^ 2 + 1) + a * c * (b ^ 3 + b ^ 2 + 1) + a * b * (c ^ 3 + c ^ 2 + 1) ≥ a * b * c * (6 + a * b + b * c + c * a)  := by
  have h0 : 0 ≤ (1 : ℝ) * (b*c) * (1 - a)^2 := by positivity
  have h1 : 0 ≤ (1 : ℝ) * (a*c) * (1 - b)^2 := by positivity
  have h2 : 0 ≤ (1 : ℝ) * (a*b) * (1 - c)^2 := by positivity
  have h3 : 0 ≤ (1 : ℝ) * (a*b*c) * (-a/2 - b/2 + c)^2 := by positivity
  have h4 : 0 ≤ (3/4 : ℝ) * (a*b*c) * (-a + b)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), b * c * (a ^ 3 + a ^ 2 + 1) + a * c * (b ^ 3 + b ^ 2 + 1) + a * b * (c ^ 3 + c ^ 2 + 1) ≥ a * b * c * (6 + a * b + b * c + c * a)) := @solution
#print axioms solution
