-- Prove2me | solution 1 for WorkbookSource.base_55508
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:53:25.743298+00:00
-- url     : https://prove2.me/submissions/22f534aa-ac1e-4526-8e05-ac0bc4fe7e61

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a + (b + 1) ^ 2 ≥ 9 * a * b / (a + b)  := by
  have hn : 0 ≤ (a^2 + a*b^2 - 6*a*b + a + b^3 + 2*b^2 + b) := by
    have hs0 : 0 ≤ (4 : ℝ) * (1) * (-a/2 + b)^2 := by positivity
    have hs1 : 0 ≤ (1 : ℝ) * (b) * (1 - b)^2 := by positivity
    have hs2 : 0 ≤ (1 : ℝ) * (a) * (1 - b)^2 := by positivity
    nlinarith only [hs0, hs1, hs2]
  have hd : (0 : ℝ) < (a + b) := by positivity
  have heqrat : ( a + (b + 1) ^ 2 ) - ( 9 * a * b / (a + b)  ) = (a^2 + a*b^2 - 6*a*b + a + b^3 + 2*b^2 + b) / (a + b) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b), a + (b + 1) ^ 2 ≥ 9 * a * b / (a + b)) := @solution
#print axioms solution
