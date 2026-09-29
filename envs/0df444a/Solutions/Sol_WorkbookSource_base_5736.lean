-- Prove2me | solution 1 for WorkbookSource.base_5736
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:37:50.264412+00:00
-- url     : https://prove2.me/submissions/7f9f7dd8-36fd-4148-8dd5-30e61f07b1c5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 + (8 * a * b * c) / (a + b) / (b + c) / (c + a) ≥ 2 * (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2)  := by
  have hn : 0 ≤ (a^4*b + a^4*c - a^3*b^2 + 6*a^3*b*c - a^3*c^2 - a^2*b^3 - 6*a^2*b^2*c - 6*a^2*b*c^2 - a^2*c^3 + a*b^4 + 6*a*b^3*c - 6*a*b^2*c^2 + 6*a*b*c^3 + a*c^4 + b^4*c - b^3*c^2 - b^2*c^3 + b*c^4) := by
    have hs0 : 0 ≤ (1 : ℝ) * (c) * (-a^2 + a*c - b^2 + b*c)^2 := by positivity
    have hs1 : 0 ≤ (1 : ℝ) * (b) * (a^2 - a*b - b*c + c^2)^2 := by positivity
    have hs2 : 0 ≤ (1 : ℝ) * (a) * (-a*b - a*c + b^2 + c^2)^2 := by positivity
    have hs3 : 0 ≤ (4 : ℝ) * (a*b*c) * (-a/2 - b/2 + c)^2 := by positivity
    have hs4 : 0 ≤ (3 : ℝ) * (a*b*c) * (-a + b)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4]
  field_simp (disch := positivity)
  nlinarith only [hn]

example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 1 + (8 * a * b * c) / (a + b) / (b + c) / (c + a) ≥ 2 * (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2)) := @solution
#print axioms solution
