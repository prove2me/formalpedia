-- Prove2me | solution 1 for WorkbookSource.plus_75988
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:18:55.256766+00:00
-- url     : https://prove2.me/submissions/4a18f1dc-0896-49d1-8b30-9d7469ea24ec

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a / b / c + b / (2 * c * a) + 1 / b ≥ 2   := by
  have hhom : 0 ≤ (2*a^3/3 + 2*a^2*b/3 + 4*a^2*c/3 + a*b^2/3 - 10*a*b*c/3 + 2*a*c^2/3 + b^3/3 + b^2*c/3) := by
    have hs0 : 0 ≤ (4/3 : ℝ) * (c) * (a - b/2)^2 := by positivity
    have hs1 : 0 ≤ (4/3 : ℝ) * (b) * (a - b/2)^2 := by positivity
    have hs2 : 0 ≤ (5/3 : ℝ) * (a) * (-a/5 + b - 3*c/5)^2 := by positivity
    have hs3 : 0 ≤ (3/5 : ℝ) * (a) * (a - c/3)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3]
  have hehom : (2*a^2 - 4*a*b*c + 2*a*c + b^2) = (2*a^3/3 + 2*a^2*b/3 + 4*a^2*c/3 + a*b^2/3 - 10*a*b*c/3 + 2*a*c^2/3 + b^3/3 + b^2*c/3) := by
    linear_combination (-2*a^2/3 - 2*a*c/3 - b^2/3) * habc
  have hn : 0 ≤ (2*a^2 - 4*a*b*c + 2*a*c + b^2) := by linarith only [hhom, hehom]
  have hd : (0 : ℝ) < (2*a*b*c) := by positivity
  have heqrat : ( a / b / c + b / (2 * c * a) + 1 / b ) - ( 2   ) = (2*a^2 - 4*a*b*c + 2*a*c + b^2) / (2*a*b*c) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), a / b / c + b / (2 * c * a) + 1 / b ≥ 2) := @solution
#print axioms solution
