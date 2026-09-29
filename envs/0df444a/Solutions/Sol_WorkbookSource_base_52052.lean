-- Prove2me | solution 1 for WorkbookSource.base_52052
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:53:24.843537+00:00
-- url     : https://prove2.me/submissions/100b577e-9108-415d-ab68-c15bbd392ce4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (1 + a) + 2 * b / (2 + b) + 3 * c / (3 + c)) ≤ 6 * (a + b + c) / (6 + a + b + c)  := by
  have hn : 0 ≤ (9*a^2*b + 4*a^2*c + 30*a^2 + 9*a*b^2 - 22*a*b*c - 12*a*b + 4*a*c^2 - 12*a*c + b^2*c + 12*b^2 + b*c^2 - 12*b*c + 6*c^2) := by
    have hs0 : 0 ≤ (30 : ℝ) * (1) * (a - b/5 - c/5)^2 := by positivity
    have hs1 : 0 ≤ (54/5 : ℝ) * (1) * (b - 2*c/3)^2 := by positivity
    have hs2 : 0 ≤ (4 : ℝ) * (c) * (a - b/2)^2 := by positivity
    have hs3 : 0 ≤ (9 : ℝ) * (b) * (a - c/3)^2 := by positivity
    have hs4 : 0 ≤ (9 : ℝ) * (a) * (b - 2*c/3)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4]
  have hd : (0 : ℝ) < ((a + 1)*(b + 2)*(c + 3)*(a + b + c + 6)) := by positivity
  have heqrat : ( 6 * (a + b + c) / (6 + a + b + c)  ) - ( (a / (1 + a) + 2 * b / (2 + b) + 3 * c / (3 + c)) ) = (9*a^2*b + 4*a^2*c + 30*a^2 + 9*a*b^2 - 22*a*b*c - 12*a*b + 4*a*c^2 - 12*a*c + b^2*c + 12*b^2 + b*c^2 - 12*b*c + 6*c^2) / ((a + 1)*(b + 2)*(c + 3)*(a + b + c + 6)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (1 + a) + 2 * b / (2 + b) + 3 * c / (3 + c)) ≤ 6 * (a + b + c) / (6 + a + b + c)) := @solution
#print axioms solution
