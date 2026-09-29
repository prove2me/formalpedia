-- Prove2me | solution 1 for WorkbookSource.base_28463
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:55:43.962637+00:00
-- url     : https://prove2.me/submissions/022d0c8f-cc47-4f3a-9be5-e6f270aaf368

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : (a^2 + 2 * b * c) * (b^2 + 2 * a * c) * (c^2 + 2 * a * b) ≥ (a * b + a * c + b * c)^3  := by
  have h0 : 0 ≤ (4 : ℝ) * (b*c) * (a^2 - 7*a*b/16 - 7*a*c/16 - b*c/8)^2 := by positivity
  have h1 : 0 ≤ (15/16 : ℝ) * (b*c) * (-a*b/2 - a*c/2 + b*c)^2 := by positivity
  have h2 : 0 ≤ (4 : ℝ) * (a*c) * (-7*a*b/16 - a*c/8 + b^2 - 7*b*c/16)^2 := by positivity
  have h3 : 0 ≤ (15/16 : ℝ) * (a*c) * (-a*b/2 + a*c - b*c/2)^2 := by positivity
  have h4 : 0 ≤ (4 : ℝ) * (a*b) * (-a*b/8 - 7*a*c/16 - 7*b*c/16 + c^2)^2 := by positivity
  have h5 : 0 ≤ (15/16 : ℝ) * (a*b) * (a*b - a*c/2 - b*c/2)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0), (a^2 + 2 * b * c) * (b^2 + 2 * a * c) * (c^2 + 2 * a * b) ≥ (a * b + a * c + b * c)^3) := @solution
#print axioms solution
