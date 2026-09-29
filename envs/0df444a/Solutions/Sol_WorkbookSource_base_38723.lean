-- Prove2me | solution 1 for WorkbookSource.base_38723
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:49:54.587302+00:00
-- url     : https://prove2.me/submissions/dc1fa24a-d7d5-436a-b3e8-eec4f47efa99

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c) / a + (2 / 125) * ((c + a) / b) ^ 2 + (a + b) / c ≥ 16 / 5  := by
  have hn : 0 ≤ (2*a^3*c + 125*a^2*b^2 + 4*a^2*c^2 + 125*a*b^3 - 400*a*b^2*c + 2*a*c^3 + 125*b^3*c + 125*b^2*c^2) := by
    have hs0 : 0 ≤ (125 : ℝ) * (1) * (-4*a*b/5 - 2*a*c/25 + b*c)^2 := by positivity
    have hs1 : 0 ≤ (45 : ℝ) * (1) * (a*b - 2*a*c/5)^2 := by positivity
    have hs2 : 0 ≤ (125 : ℝ) * (b*c) * (-2*a/5 + b)^2 := by positivity
    have hs3 : 0 ≤ (2 : ℝ) * (a*c) * (-a + c)^2 := by positivity
    have hs4 : 0 ≤ (125 : ℝ) * (a*b) * (b - 2*c/5)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4]
  have hd : (0 : ℝ) < (125*a*b^2*c) := by positivity
  have heqrat : ( (b + c) / a + (2 / 125) * ((c + a) / b) ^ 2 + (a + b) / c ) - ( 16 / 5  ) = (2*a^3*c + 125*a^2*b^2 + 4*a^2*c^2 + 125*a*b^3 - 400*a*b^2*c + 2*a*c^3 + 125*b^3*c + 125*b^2*c^2) / (125*a*b^2*c) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (b + c) / a + (2 / 125) * ((c + a) / b) ^ 2 + (a + b) / c ≥ 16 / 5) := @solution
#print axioms solution
