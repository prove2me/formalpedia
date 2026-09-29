-- Prove2me | solution 1 for WorkbookSource.base_29761
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:45:29.434727+00:00
-- url     : https://prove2.me/submissions/e810da4a-44d0-4d9e-bacc-1f5aa125b970

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / b^2 + b / (c + a) + c / b) ≥ 7 / 4  := by
  have hn : 0 ≤ (4*a^3 + 4*a^2*c - 7*a*b^2 + 4*a*b*c + 4*b^3 - 7*b^2*c + 4*b*c^2) := by
    have hs0 : 0 ≤ (4 : ℝ) * (c) * (a - b/2)^2 := by positivity
    have hs1 : 0 ≤ (4 : ℝ) * (b) * (a - b + c)^2 := by positivity
    have hs2 : 0 ≤ (4 : ℝ) * (a) * (a - b/2)^2 := by positivity
    nlinarith only [hs0, hs1, hs2]
  have hd : (0 : ℝ) < (4*b^2*(a + c)) := by positivity
  have heqrat : ( (a^2 / b^2 + b / (c + a) + c / b) ) - ( 7 / 4  ) = (4*a^3 + 4*a^2*c - 7*a*b^2 + 4*a*b*c + 4*b^3 - 7*b^2*c + 4*b*c^2) / (4*b^2*(a + c)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 / b^2 + b / (c + a) + c / b) ≥ 7 / 4) := @solution
#print axioms solution
