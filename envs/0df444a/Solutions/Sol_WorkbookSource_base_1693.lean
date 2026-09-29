-- Prove2me | solution 1 for WorkbookSource.base_1693
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:41:38.121198+00:00
-- url     : https://prove2.me/submissions/4c94d95e-410a-4bba-a5be-2ef5aed81ec6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (c / (a + b) + d / (b + c) + a / (c + d) + b / (d + a)) ≥ 2  := by
  have hn : 0 ≤ (a^3*b + a^3*c + a^2*b^2 - a^2*b*c - a^2*b*d - 2*a^2*c^2 + a^2*d^2 - a*b^2*c - a*b*d^2 + a*c^3 - a*c^2*d - a*c*d^2 + a*d^3 + b^3*c + b^3*d + b^2*c^2 - b^2*c*d - 2*b^2*d^2 - b*c^2*d + b*d^3 + c^3*d + c^2*d^2) := by
    have hs0 : 0 ≤ (1 : ℝ) * (1) * (a*b/4 - 5*a*d/8 - 5*b*c/8 + c*d)^2 := by positivity
    have hs1 : 0 ≤ (15/16 : ℝ) * (1) * (a*b - a*d/2 - b*c/2)^2 := by positivity
    have hs2 : 0 ≤ (3/8 : ℝ) * (1) * (-a*d + b*c)^2 := by positivity
    have hs3 : 0 ≤ (1 : ℝ) * (c*d) * (-a + c)^2 := by positivity
    have hs4 : 0 ≤ (1 : ℝ) * (b*d) * (a/2 - b - c/2 + d)^2 := by positivity
    have hs5 : 0 ≤ (1 : ℝ) * (b*c) * (-b + d)^2 := by positivity
    have hs6 : 0 ≤ (1 : ℝ) * (a*d) * (-b + d)^2 := by positivity
    have hs7 : 0 ≤ (1 : ℝ) * (a*c) * (-a - b/2 + c + d/2)^2 := by positivity
    have hs8 : 0 ≤ (1 : ℝ) * (a*b) * (-a + c)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8]
  have hd : 0 < ((a + b)*(a + d)*(b + c)*(c + d)) := by positivity
  have heqrat : ( (c / (a + b) + d / (b + c) + a / (c + d) + b / (d + a)) ) - ( 2  ) = (a^3*b + a^3*c + a^2*b^2 - a^2*b*c - a^2*b*d - 2*a^2*c^2 + a^2*d^2 - a*b^2*c - a*b*d^2 + a*c^3 - a*c^2*d - a*c*d^2 + a*d^3 + b^3*c + b^3*d + b^2*c^2 - b^2*c*d - 2*b^2*d^2 - b*c^2*d + b*d^3 + c^3*d + c^2*d^2) / ((a + b)*(a + d)*(b + c)*(c + d)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (c / (a + b) + d / (b + c) + a / (c + d) + b / (d + a)) ≥ 2) := @solution
#print axioms solution
