-- Prove2me | solution 1 for WorkbookSource.plus_41300
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:53:26.999437+00:00
-- url     : https://prove2.me/submissions/6072276c-4ed5-4aaf-a23c-b41312769dff

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a + b + c + (a * b + b * c + c * a - 2) ^ 2 / (a + b + c) ≥ 20 / 9   := by
  have hn : 0 ≤ (9*a^2*b^2 + 18*a^2*b*c + 9*a^2*c^2 + 9*a^2 + 18*a*b^2*c + 18*a*b*c^2 - 18*a*b - 18*a*c - 20*a + 9*b^2*c^2 + 9*b^2 - 18*b*c - 20*b + 9*c^2 - 20*c + 36) := by
    have hs0 : 0 ≤ (36 : ℝ) * (1) * (-a*b/3 - a*c/3 - 5*a/18 - b*c/3 - 5*b/18 - 5*c/18 + 1)^2 := by positivity
    have hs1 : 0 ≤ (56/9 : ℝ) * (1) * (-15*a*b/28 - 15*a*c/28 + a/28 - 15*b*c/28 + b/28 + c)^2 := by positivity
    have hs2 : 0 ≤ (87/14 : ℝ) * (1) * (-15*a*b/29 - 15*a*c/29 + a/29 - 15*b*c/29 + b)^2 := by positivity
    have hs3 : 0 ≤ (180/29 : ℝ) * (1) * (-a*b/2 - a*c/2 + a - b*c/2)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3]
  have hd : (0 : ℝ) < (9*a + 9*b + 9*c) := by positivity
  have heqrat : ( a + b + c + (a * b + b * c + c * a - 2) ^ 2 / (a + b + c) ) - ( 20 / 9   ) = (9*a^2*b^2 + 18*a^2*b*c + 9*a^2*c^2 + 9*a^2 + 18*a*b^2*c + 18*a*b*c^2 - 18*a*b - 18*a*c - 20*a + 9*b^2*c^2 + 9*b^2 - 18*b*c - 20*b + 9*c^2 - 20*c + 36) / (9*a + 9*b + 9*c) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a + b + c + (a * b + b * c + c * a - 2) ^ 2 / (a + b + c) ≥ 20 / 9) := @solution
#print axioms solution
