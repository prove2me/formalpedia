-- Prove2me | solution 1 for WorkbookSource.base_34828
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:55:47.012303+00:00
-- url     : https://prove2.me/submissions/1e5c2fc9-4926-43d4-9940-eb794174f2ae

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 3 * (a^3 + b^3 + c^3 + a * b * c) ≥ 4 * (a^2 * b + b^2 * c + c^2 * a)  := by
  have h0 : 0 ≤ (3 : ℝ) * (c) * (-13*a/18 - 5*b/18 + c)^2 := by positivity
  have h1 : 0 ≤ (11/108 : ℝ) * (c) * (-a + b)^2 := by positivity
  have h2 : 0 ≤ (3 : ℝ) * (b) * (-5*a/18 + b - 13*c/18)^2 := by positivity
  have h3 : 0 ≤ (11/108 : ℝ) * (b) * (-a + c)^2 := by positivity
  have h4 : 0 ≤ (3 : ℝ) * (a) * (a - 13*b/18 - 5*c/18)^2 := by positivity
  have h5 : 0 ≤ (11/108 : ℝ) * (a) * (-b + c)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 3 * (a^3 + b^3 + c^3 + a * b * c) ≥ 4 * (a^2 * b + b^2 * c + c^2 * a)) := @solution
#print axioms solution
