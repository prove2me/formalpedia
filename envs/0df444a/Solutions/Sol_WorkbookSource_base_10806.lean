-- Prove2me | solution 1 for WorkbookSource.base_10806
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:44:18.825495+00:00
-- url     : https://prove2.me/submissions/29ace3c4-fe1a-46bb-bf0a-1e4a1fe84a43

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a / (b + 2 * c + d) + b / (c + 2 * d + a) + c / (d + 2 * a + b) + d / (a + 2 * b + c)) ≥ 1  := by
  have hn : 0 ≤ (2*a^4 + 3*a^3*b + 3*a^3*d - a^2*b^2 - 3*a^2*b*c + 6*a^2*b*d - 4*a^2*c^2 - 3*a^2*c*d - a^2*d^2 + 3*a*b^3 + 6*a*b^2*c - 3*a*b^2*d - 3*a*b*c^2 - 20*a*b*c*d - 3*a*b*d^2 - 3*a*c^2*d + 6*a*c*d^2 + 3*a*d^3 + 2*b^4 + 3*b^3*c - b^2*c^2 - 3*b^2*c*d - 4*b^2*d^2 + 3*b*c^3 + 6*b*c^2*d - 3*b*c*d^2 + 2*c^4 + 3*c^3*d - c^2*d^2 + 3*c*d^3 + 2*d^4) := by
    have hs0 : 0 ≤ (2 : ℝ) * (1) * (-a*b/2 + a*d/2 - b^2 - b*c/2 + c*d/2 + d^2)^2 := by positivity
    have hs1 : 0 ≤ (2 : ℝ) * (1) * (-a^2 - a*b/2 - a*d/2 + b*c/2 + c^2 + c*d/2)^2 := by positivity
    have hs2 : 0 ≤ (1 : ℝ) * (c*d) * (a - b - c + d)^2 := by positivity
    have hs3 : 0 ≤ (2 : ℝ) * (b*d) * (-a + c)^2 := by positivity
    have hs4 : 0 ≤ (1 : ℝ) * (b*c) * (-a - b + c + d)^2 := by positivity
    have hs5 : 0 ≤ (1 : ℝ) * (a*d) * (-a - b + c + d)^2 := by positivity
    have hs6 : 0 ≤ (2 : ℝ) * (a*c) * (-b + d)^2 := by positivity
    have hs7 : 0 ≤ (1 : ℝ) * (a*b) * (a - b - c + d)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7]
  have hd : 0 < ((a + 2*b + c)*(a + c + 2*d)*(2*a + b + d)*(b + 2*c + d)) := by positivity
  have heqrat : ( (a / (b + 2 * c + d) + b / (c + 2 * d + a) + c / (d + 2 * a + b) + d / (a + 2 * b + c)) ) - ( 1  ) = (2*a^4 + 3*a^3*b + 3*a^3*d - a^2*b^2 - 3*a^2*b*c + 6*a^2*b*d - 4*a^2*c^2 - 3*a^2*c*d - a^2*d^2 + 3*a*b^3 + 6*a*b^2*c - 3*a*b^2*d - 3*a*b*c^2 - 20*a*b*c*d - 3*a*b*d^2 - 3*a*c^2*d + 6*a*c*d^2 + 3*a*d^3 + 2*b^4 + 3*b^3*c - b^2*c^2 - 3*b^2*c*d - 4*b^2*d^2 + 3*b*c^3 + 6*b*c^2*d - 3*b*c*d^2 + 2*c^4 + 3*c^3*d - c^2*d^2 + 3*c*d^3 + 2*d^4) / ((a + 2*b + c)*(a + c + 2*d)*(2*a + b + d)*(b + 2*c + d)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (a / (b + 2 * c + d) + b / (c + 2 * d + a) + c / (d + 2 * a + b) + d / (a + 2 * b + c)) ≥ 1) := @solution
#print axioms solution
