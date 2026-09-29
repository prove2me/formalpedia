-- Prove2me | solution 1 for WorkbookSource.base_53202
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:03:31.114616+00:00
-- url     : https://prove2.me/submissions/dc97b6db-037b-4f83-a622-3989862034be

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b) * (b^2 + c) * (c^2 + a) ≥ a * b * c * (a + 1) * (b + 1) * (c + 1)  := by
  have h0 : 0 ≤ (1 : ℝ) * (c) * (-a*b + a*c)^2 := by positivity
  have h1 : 0 ≤ (1 : ℝ) * (b) * (-a*c + b*c)^2 := by positivity
  have h2 : 0 ≤ (1 : ℝ) * (b*c) * (-a + c)^2 := by positivity
  have h3 : 0 ≤ (1 : ℝ) * (a) * (-a*b + b*c)^2 := by positivity
  have h4 : 0 ≤ (1 : ℝ) * (a*c) * (-a + b)^2 := by positivity
  have h5 : 0 ≤ (1 : ℝ) * (a*b) * (-b + c)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b) * (b^2 + c) * (c^2 + a) ≥ a * b * c * (a + 1) * (b + 1) * (c + 1)) := @solution
#print axioms solution
