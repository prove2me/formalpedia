-- Prove2me | solution 1 for WorkbookSource.base_18091
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:54:44.455035+00:00
-- url     : https://prove2.me/submissions/3d6ff018-92b0-4848-ae84-f1ccc76f7bbe

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + (a + b) / c) * (b / (c + a) + (b + c) / a) * (c / (a + b) + (c + a) / b) ≥ 125 / 8  := by
  have hn : 0 ≤ (16*a^4*b^2 + 40*a^4*b*c + 16*a^4*c^2 + 32*a^3*b^3 - 37*a^3*b^2*c - 37*a^3*b*c^2 + 32*a^3*c^3 + 16*a^2*b^4 - 37*a^2*b^3*c - 90*a^2*b^2*c^2 - 37*a^2*b*c^3 + 16*a^2*c^4 + 40*a*b^4*c - 37*a*b^3*c^2 - 37*a*b^2*c^3 + 40*a*b*c^4 + 16*b^4*c^2 + 32*b^3*c^3 + 16*b^2*c^4) := by
    have hs0 : 0 ≤ (16 : ℝ) * (1) * (-a^2*b - a^2*c/2 - a*b^2/2 + a*c^2/2 + b^2*c/2 + b*c^2)^2 := by positivity
    have hs1 : 0 ≤ (12 : ℝ) * (1) * (-a^2*c + a*b^2 - a*c^2 + b^2*c)^2 := by positivity
    have hs2 : 0 ≤ (24 : ℝ) * (b*c) * (a^2 - 3*a*b/8 - 3*a*c/8 - b*c/4)^2 := by positivity
    have hs3 : 0 ≤ (29/2 : ℝ) * (b*c) * (-a*b/2 - a*c/2 + b*c)^2 := by positivity
    have hs4 : 0 ≤ (24 : ℝ) * (a*c) * (-3*a*b/8 - a*c/4 + b^2 - 3*b*c/8)^2 := by positivity
    have hs5 : 0 ≤ (29/2 : ℝ) * (a*c) * (-a*b/2 + a*c - b*c/2)^2 := by positivity
    have hs6 : 0 ≤ (24 : ℝ) * (a*b) * (-a*b/4 - 3*a*c/8 - 3*b*c/8 + c^2)^2 := by positivity
    have hs7 : 0 ≤ (29/2 : ℝ) * (a*b) * (a*b - a*c/2 - b*c/2)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (b + c) + (a + b) / c) * (b / (c + a) + (b + c) / a) * (c / (a + b) + (c + a) / b) ≥ 125 / 8) := @solution
#print axioms solution
