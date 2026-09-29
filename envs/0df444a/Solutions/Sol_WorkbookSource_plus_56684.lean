-- Prove2me | solution 1 for WorkbookSource.plus_56684
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:55:34.80418+00:00
-- url     : https://prove2.me/submissions/f97f7629-a3c6-4bbe-ac1f-c1bbd47ab82b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b + 2 * b * c / (a + b) + 2 * b / (c * (a + b)) ≥ 3   := by
  have hn : 0 ≤ (a^2*c - 2*a*b*c + 2*b^2*c^2 - 3*b^2*c + 2*b^2) := by
    have hs0 : 0 ≤ (2 : ℝ) * (1) * (-b*c + b)^2 := by positivity
    have hs1 : 0 ≤ (1 : ℝ) * (c) * (-a + b)^2 := by positivity
    nlinarith only [hs0, hs1]
  have hd : (0 : ℝ) < (b*c*(a + b)) := by positivity
  have heqrat : ( a / b + 2 * b * c / (a + b) + 2 * b / (c * (a + b)) ) - ( 3   ) = (a^2*c - 2*a*b*c + 2*b^2*c^2 - 3*b^2*c + 2*b^2) / (b*c*(a + b)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a / b + 2 * b * c / (a + b) + 2 * b / (c * (a + b)) ≥ 3) := @solution
#print axioms solution
