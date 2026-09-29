-- Prove2me | solution 1 for WorkbookSource.base_15960
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:37.026921+00:00
-- url     : https://prove2.me/submissions/98bb4b12-6f68-4ec2-99ce-7e31fb1304a3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b)) ≥ 3 / 2 + (a - b) ^ 2 / (2 * (a + b) ^ 2)  := by
  have hn : 0 ≤ (a^4 - a^3*c - a^2*c^2 + a*c^3 + b^4 - b^3*c - b^2*c^2 + b*c^3) := by
    have hs0 : 0 ≤ (1 : ℝ) * (1) * (-b^2 + b*c)^2 := by positivity
    have hs1 : 0 ≤ (1 : ℝ) * (1) * (-a^2 + a*c)^2 := by positivity
    have hs2 : 0 ≤ (1 : ℝ) * (b*c) * (-b + c)^2 := by positivity
    have hs3 : 0 ≤ (1 : ℝ) * (a*c) * (-a + c)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (b + c) + b / (c + a) + c / (a + b)) ≥ 3 / 2 + (a - b) ^ 2 / (2 * (a + b) ^ 2)) := @solution
#print axioms solution
