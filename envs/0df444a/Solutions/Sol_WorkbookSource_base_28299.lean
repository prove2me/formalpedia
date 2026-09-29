-- Prove2me | solution 1 for WorkbookSource.base_28299
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:55:43.301178+00:00
-- url     : https://prove2.me/submissions/f837e053-69fd-43b6-8504-40d49783c9fd

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 2 * (a + b) * (b + c) * (c + a) ≤ 4 * (a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c) * (a * b + b * c + c * a)  := by
  have h0 : 0 ≤ (3 : ℝ) * (c) * (a^2/3 - a*c/3 - b^2 + b*c)^2 := by positivity
  have h1 : 0 ≤ (8/3 : ℝ) * (c) * (-a^2 + a*c)^2 := by positivity
  have h2 : 0 ≤ (3 : ℝ) * (b) * (-a^2/3 + a*b/3 - b*c + c^2)^2 := by positivity
  have h3 : 0 ≤ (8/3 : ℝ) * (b) * (-a^2 + a*b)^2 := by positivity
  have h4 : 0 ≤ (3 : ℝ) * (a) * (a*b/3 - a*c - b^2/3 + c^2)^2 := by positivity
  have h5 : 0 ≤ (8/3 : ℝ) * (a) * (-a*b + b^2)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b + c) ^ 2 * (a + b) * (b + c) * (c + a) ≤ 4 * (a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c) * (a * b + b * c + c * a)) := @solution
#print axioms solution
