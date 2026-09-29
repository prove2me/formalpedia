-- Prove2me | solution 1 for WorkbookSource.base_39559
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:45:35.812682+00:00
-- url     : https://prove2.me/submissions/cf663a31-5446-41a7-b905-64e191404372

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a / b + b / c + c / a ≥ 12 / (3 * a * b * c + 1)  := by
  have hhom : 0 ≤ (a^5*c/27 + a^4*b^2/27 - a^4*b*c/3 + a^4*c^2/9 + a^3*b^3/9 - 10*a^3*b^2*c/9 + 52*a^3*b*c^2/27 + a^3*c^3/9 + a^2*b^4/9 + 52*a^2*b^3*c/27 - 7*a^2*b^2*c^2/3 - 10*a^2*b*c^3/9 + a^2*c^4/27 + a*b^5/27 - a*b^4*c/3 - 10*a*b^3*c^2/9 + 52*a*b^2*c^3/27 - a*b*c^4/3 + b^4*c^2/27 + b^3*c^3/9 + b^2*c^4/9 + b*c^5/27) := by
    have hs0 : 0 ≤ (7/27 : ℝ) * (1) * (5*a^2*b/14 - a^2*c/2 - a*b^2/2 - 2*a*c^2/7 - b^2*c/14 + b*c^2)^2 := by positivity
    have hs1 : 0 ≤ (7/36 : ℝ) * (1) * (a^2*b/7 - a^2*c + a*b^2 + 2*a*c^2/7 - 3*b^2*c/7)^2 := by positivity
    have hs2 : 0 ≤ (25/27 : ℝ) * (b*c) * (-a^2/5 + a*b - 3*a*c/5 - 2*b*c/5 + c^2/5)^2 := by positivity
    have hs3 : 0 ≤ (25/27 : ℝ) * (a*c) * (a^2/5 - 3*a*b/5 - 2*a*c/5 - b^2/5 + b*c)^2 := by positivity
    have hs4 : 0 ≤ (25/27 : ℝ) * (a*b) * (-2*a*b/5 + a*c + b^2/5 - 3*b*c/5 - c^2/5)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4]
  have hehom : (3*a^3*b*c^2 + 3*a^2*b^3*c + a^2*c + 3*a*b^2*c^3 + a*b^2 - 12*a*b*c + b*c^2) = (a^5*c/27 + a^4*b^2/27 - a^4*b*c/3 + a^4*c^2/9 + a^3*b^3/9 - 10*a^3*b^2*c/9 + 52*a^3*b*c^2/27 + a^3*c^3/9 + a^2*b^4/9 + 52*a^2*b^3*c/27 - 7*a^2*b^2*c^2/3 - 10*a^2*b*c^3/9 + a^2*c^4/27 + a*b^5/27 - a*b^4*c/3 - 10*a*b^3*c^2/9 + 52*a*b^2*c^3/27 - a*b*c^4/3 + b^4*c^2/27 + b^3*c^3/9 + b^2*c^4/9 + b*c^5/27) := by
    linear_combination (-a^4*c/27 - a^3*b^2/27 + 10*a^3*b*c/27 - 2*a^3*c^2/27 - a^3*c/9 - 2*a^2*b^3/27 + 7*a^2*b^2*c/9 - a^2*b^2/9 + 7*a^2*b*c^2/9 + 11*a^2*b*c/9 - a^2*c^3/27 - a^2*c^2/9 - a^2*c/3 - a*b^4/27 + 10*a*b^3*c/27 - a*b^3/9 + 7*a*b^2*c^2/9 + 11*a*b^2*c/9 - a*b^2/3 + 10*a*b*c^3/27 + 11*a*b*c^2/9 + 4*a*b*c - b^3*c^2/27 - 2*b^2*c^3/27 - b^2*c^2/9 - b*c^4/27 - b*c^3/9 - b*c^2/3) * habc
  have hn : 0 ≤ (3*a^3*b*c^2 + 3*a^2*b^3*c + a^2*c + 3*a*b^2*c^3 + a*b^2 - 12*a*b*c + b*c^2) := by linarith only [hhom, hehom]
  have hd : 0 < (a*b*c*(3*a*b*c + 1)) := by positivity
  have heqrat : ( a / b + b / c + c / a ) - ( 12 / (3 * a * b * c + 1)  ) = (3*a^3*b*c^2 + 3*a^2*b^3*c + a^2*c + 3*a*b^2*c^3 + a*b^2 - 12*a*b*c + b*c^2) / (a*b*c*(3*a*b*c + 1)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), a / b + b / c + c / a ≥ 12 / (3 * a * b * c + 1)) := @solution
#print axioms solution
