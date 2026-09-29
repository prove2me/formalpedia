-- Prove2me | solution 1 for WorkbookSource.base_22582
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:41:35.911838+00:00
-- url     : https://prove2.me/submissions/fa3e6959-f878-4e12-91af-f27e6161e871

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a^2 + b^2 + 1) / (a + 1) / (b + 1) + 2 * a * b / (a * b * (a * b + 3)) ≥ 5 / 4  := by
  have hn : 0 ≤ (4*a^3*b - 5*a^2*b^2 - 5*a^2*b + 12*a^2 + 4*a*b^3 - 5*a*b^2 - 8*a*b - 7*a + 12*b^2 - 7*b + 5) := by
    have hs0 : 0 ≤ (12 : ℝ) * (1) * (-47*a*b/264 - 35*a/66 + b - 7/24)^2 := by positivity
    have hs1 : 0 ≤ (3131/363 : ℝ) * (1) * (-47*a*b/124 + a - 77/124)^2 := by positivity
    have hs2 : 0 ≤ (81/124 : ℝ) * (1) * (-a*b + 1)^2 := by positivity
    have hs3 : 0 ≤ (4 : ℝ) * (a*b) * (-10*a/11 + b - 1/11)^2 := by positivity
    have hs4 : 0 ≤ (84/121 : ℝ) * (a*b) * (1 - a)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4]
  have hd : 0 < (4*(a + 1)*(b + 1)*(a*b + 3)) := by positivity
  have heqrat : ( (a^2 + b^2 + 1) / (a + 1) / (b + 1) + 2 * a * b / (a * b * (a * b + 3)) ) - ( 5 / 4  ) = (4*a^3*b - 5*a^2*b^2 - 5*a^2*b + 12*a^2 + 4*a*b^3 - 5*a*b^2 - 8*a*b - 7*a + 12*b^2 - 7*b + 5) / (4*(a + 1)*(b + 1)*(a*b + 3)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b), (a^2 + b^2 + 1) / (a + 1) / (b + 1) + 2 * a * b / (a * b * (a * b + 3)) ≥ 5 / 4) := @solution
#print axioms solution
