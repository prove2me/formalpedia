-- Prove2me | solution 1 for WorkbookSource.plus_22853
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:43.673986+00:00
-- url     : https://prove2.me/submissions/6e1b2fda-a7cb-4794-b084-006d64c1e760

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (5 * a ^ 2 + b * c) * (5 * b ^ 2 + a * c) * (5 * c ^ 2 + a * b) ≥ 8 * (a * b + b * c + c * a) ^ 3   := by
  have h0 : 0 ≤ (17 : ℝ) * (b*c) * (5*a^2/17 - 11*a*b/17 - 11*a*c/17 + b*c)^2 := by positivity
  have h1 : 0 ≤ (60/17 : ℝ) * (b*c) * (a^2 - a*b/2 - a*c/2)^2 := by positivity
  have h2 : 0 ≤ (17 : ℝ) * (a*c) * (-11*a*b/17 + a*c + 5*b^2/17 - 11*b*c/17)^2 := by positivity
  have h3 : 0 ≤ (60/17 : ℝ) * (a*c) * (-a*b/2 + b^2 - b*c/2)^2 := by positivity
  have h4 : 0 ≤ (17 : ℝ) * (a*b) * (a*b - 11*a*c/17 - 11*b*c/17 + 5*c^2/17)^2 := by positivity
  have h5 : 0 ≤ (60/17 : ℝ) * (a*b) * (-a*c/2 - b*c/2 + c^2)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (5 * a ^ 2 + b * c) * (5 * b ^ 2 + a * c) * (5 * c ^ 2 + a * b) ≥ 8 * (a * b + b * c + c * a) ^ 3) := @solution
#print axioms solution
