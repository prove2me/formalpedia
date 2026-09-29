-- Prove2me | solution 1 for WorkbookSource.plus_10841
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:03:33.076964+00:00
-- url     : https://prove2.me/submissions/031050a6-9192-48cb-94ee-1a3aa69a3673

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3)*(a + b)*(b + c)*(c + a) ≥ 3 * (a^2 + b * c)*(b^2 + c * a)*(c^2 + a * b)   := by
  have h0 : 0 ≤ (1 : ℝ) * (1) * (-a^2*b + a^2*c/2 + a*b^2/2 - a*c^2/2 - b^2*c/2 + b*c^2)^2 := by positivity
  have h1 : 0 ≤ (3/4 : ℝ) * (1) * (-a^2*c - a*b^2/3 + a*c^2/3 + b^2*c)^2 := by positivity
  have h2 : 0 ≤ (2/3 : ℝ) * (1) * (-a*b^2 + a*c^2)^2 := by positivity
  have h3 : 0 ≤ (1 : ℝ) * (b*c) * (-b^2 + c^2)^2 := by positivity
  have h4 : 0 ≤ (1 : ℝ) * (a*c) * (-a^2 + c^2)^2 := by positivity
  have h5 : 0 ≤ (1 : ℝ) * (a*b) * (-a^2 + b^2)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 + b^3 + c^3)*(a + b)*(b + c)*(c + a) ≥ 3 * (a^2 + b * c)*(b^2 + c * a)*(c^2 + a * b)) := @solution
#print axioms solution
