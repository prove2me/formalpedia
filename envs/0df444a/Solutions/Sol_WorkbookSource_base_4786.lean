-- Prove2me | solution 1 for WorkbookSource.base_4786
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:04:10.800979+00:00
-- url     : https://prove2.me/submissions/1569387a-754e-496c-9240-a9228280ab9c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a + b + c) ^ 2 * (a + b) * (a + c) * (b + c) ≥ 24 * a * b * c * (a ^ 2 + b ^ 2 + c ^ 2)  := by
  have h0 : 0 ≤ (9 : ℝ) * (c) * (a^2/3 - a*c - b^2/3 + b*c)^2 := by positivity
  have h1 : 0 ≤ (9 : ℝ) * (b) * (a^2/3 - a*b + b*c - c^2/3)^2 := by positivity
  have h2 : 0 ≤ (9 : ℝ) * (a) * (-a*b + a*c + b^2/3 - c^2/3)^2 := by positivity
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c), (a + b + c) ^ 2 * (a + b) * (a + c) * (b + c) ≥ 24 * a * b * c * (a ^ 2 + b ^ 2 + c ^ 2)) := @solution
#print axioms solution
