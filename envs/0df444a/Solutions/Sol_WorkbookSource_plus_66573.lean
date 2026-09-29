-- Prove2me | solution 1 for WorkbookSource.plus_66573
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:55:35.771824+00:00
-- url     : https://prove2.me/submissions/0d745f17-cf8a-4338-a8f5-584bafc25976

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 + a * b / (c + a)) * (1 + 2 * a / (b * (c + a)) + c / a) ≥ 9 / 2   := by
  have hn : 0 ≤ (2*a^3*b^2 - 3*a^3*b + 4*a^3 + 4*a^2*b^2*c - 12*a^2*b*c + 4*a^2*c + 2*a*b^2*c^2 - 3*a*b*c^2 + 2*b*c^3) := by
    have hs0 : 0 ≤ (4 : ℝ) * (c) * (-a*b + a)^2 := by positivity
    have hs1 : 0 ≤ (2 : ℝ) * (b*c) * (-a + c)^2 := by positivity
    have hs2 : 0 ≤ (4 : ℝ) * (a) * (-a*b/2 + a - b*c/2)^2 := by positivity
    have hs3 : 0 ≤ (1 : ℝ) * (a) * (-a*b + b*c)^2 := by positivity
    have hs4 : 0 ≤ (1 : ℝ) * (a*b) * (-a + c)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4]
  have hd : (0 : ℝ) < (2*a*b*(a + c)^2) := by positivity
  have heqrat : ( (1 + a * b / (c + a)) * (1 + 2 * a / (b * (c + a)) + c / a) ) - ( 9 / 2   ) = (2*a^3*b^2 - 3*a^3*b + 4*a^3 + 4*a^2*b^2*c - 12*a^2*b*c + 4*a^2*c + 2*a*b^2*c^2 - 3*a*b*c^2 + 2*b*c^3) / (2*a*b*(a + c)^2) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 + a * b / (c + a)) * (1 + 2 * a / (b * (c + a)) + c / a) ≥ 9 / 2) := @solution
#print axioms solution
