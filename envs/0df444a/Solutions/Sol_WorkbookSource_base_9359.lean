-- Prove2me | solution 1 for WorkbookSource.base_9359
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:44:32.117758+00:00
-- url     : https://prove2.me/submissions/1d1629ee-28e8-4918-960a-cf75d4bfa584

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b) / (a + b + 2 * c) + (b * c) / (b + c + 2 * a) + (c * a) / (c + a + 2 * b) ≤ (1 / 4) * (a + b + c)  := by
  have hn : 0 ≤ (2*a^4 + a^3*b + a^3*c - 6*a^2*b^2 + 2*a^2*b*c - 6*a^2*c^2 + a*b^3 + 2*a*b^2*c + 2*a*b*c^2 + a*c^3 + 2*b^4 + b^3*c - 6*b^2*c^2 + b*c^3 + 2*c^4) := by
    have hs0 : 0 ≤ (2 : ℝ) * (1) * (-a^2/2 + a*b - a*c/2 - b^2/2 - b*c/2 + c^2)^2 := by positivity
    have hs1 : 0 ≤ (3/2 : ℝ) * (1) * (a^2 - a*c - b^2 + b*c)^2 := by positivity
    have hs2 : 0 ≤ (3 : ℝ) * (b*c) * (-b + c)^2 := by positivity
    have hs3 : 0 ≤ (3 : ℝ) * (a*c) * (-a + c)^2 := by positivity
    have hs4 : 0 ≤ (3 : ℝ) * (a*b) * (-a + b)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * b) / (a + b + 2 * c) + (b * c) / (b + c + 2 * a) + (c * a) / (c + a + 2 * b) ≤ (1 / 4) * (a + b + c)) := @solution
#print axioms solution
