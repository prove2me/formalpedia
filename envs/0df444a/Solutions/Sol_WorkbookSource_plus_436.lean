-- Prove2me | solution 1 for WorkbookSource.plus_436
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:03:32.470599+00:00
-- url     : https://prove2.me/submissions/3353e9f6-916c-40fe-b2b8-691258a99a34

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : b^3 * a + a^4 + c^4 ≥ a * b * c * (c + b) + a^3 * c   := by
  have h0 : 0 ≤ (1 : ℝ) * (1) * (-3*a^2/8 - 5*a*b/8 + c^2)^2 := by positivity
  have h1 : 0 ≤ (55/64 : ℝ) * (1) * (a^2 - 23*a*b/55 - 32*a*c/55)^2 := by positivity
  have h2 : 0 ≤ (101/220 : ℝ) * (1) * (-a*b + a*c)^2 := by positivity
  have h3 : 0 ≤ (1 : ℝ) * (a*b) * (-a/2 + b - c/2)^2 := by positivity
  nlinarith only [h0, h1, h2, h3]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c), b^3 * a + a^4 + c^4 ≥ a * b * c * (c + b) + a^3 * c) := @solution
#print axioms solution
