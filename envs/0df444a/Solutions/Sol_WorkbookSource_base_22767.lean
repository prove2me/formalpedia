-- Prove2me | solution 1 for WorkbookSource.base_22767
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:41:36.490457+00:00
-- url     : https://prove2.me/submissions/756519ec-11c2-4ade-ab14-8bf3a53658c4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) ^ 2 + (a + b - 16 / 3 * c) ^ 2 ≥ 200 / 9 * (a * b * c) / (a + b + c)  := by
  have hn : 0 ≤ (18*a^3 + 54*a^2*b - 78*a^2*c + 54*a*b^2 - 356*a*b*c + 160*a*c^2 + 18*b^3 - 78*b^2*c + 160*b*c^2 + 256*c^3) := by
    have hs0 : 0 ≤ (256 : ℝ) * (c) * (-a/4 - b/4 + c)^2 := by positivity
    have hs1 : 0 ≤ (288 : ℝ) * (b) * (-97*a/288 - 47*b/288 + c)^2 := by positivity
    have hs2 : 0 ≤ (2975/288 : ℝ) * (b) * (-a + b)^2 := by positivity
    have hs3 : 0 ≤ (288 : ℝ) * (a) * (-47*a/288 - 97*b/288 + c)^2 := by positivity
    have hs4 : 0 ≤ (2975/288 : ℝ) * (a) * (-a + b)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4]
  have hd : 0 < (9*a + 9*b + 9*c) := by positivity
  have heqrat : ( (a + b) ^ 2 + (a + b - 16 / 3 * c) ^ 2 ) - ( 200 / 9 * (a * b * c) / (a + b + c)  ) = (18*a^3 + 54*a^2*b - 78*a^2*c + 54*a*b^2 - 356*a*b*c + 160*a*c^2 + 18*b^3 - 78*b^2*c + 160*b*c^2 + 256*c^3) / (9*a + 9*b + 9*c) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) ^ 2 + (a + b - 16 / 3 * c) ^ 2 ≥ 200 / 9 * (a * b * c) / (a + b + c)) := @solution
#print axioms solution
