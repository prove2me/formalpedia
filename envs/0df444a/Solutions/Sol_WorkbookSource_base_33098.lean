-- Prove2me | solution 1 for WorkbookSource.base_33098
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:49:57.938749+00:00
-- url     : https://prove2.me/submissions/97f1f75b-4edd-4a4b-be2c-fff1fcbc4e46

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (1 / a + 1 / b + 1 / c + 1 / d) ≥ 16 / (a + b + c + d)  := by
  have hn : 0 ≤ (a^2*b*c + a^2*b*d + a^2*c*d + a*b^2*c + a*b^2*d + a*b*c^2 - 12*a*b*c*d + a*b*d^2 + a*c^2*d + a*c*d^2 + b^2*c*d + b*c^2*d + b*c*d^2) := by
    have hs0 : 0 ≤ (1 : ℝ) * (c*d) * (-a + b)^2 := by positivity
    have hs1 : 0 ≤ (1 : ℝ) * (b*d) * (-a + c)^2 := by positivity
    have hs2 : 0 ≤ (1 : ℝ) * (b*c) * (-a + d)^2 := by positivity
    have hs3 : 0 ≤ (1 : ℝ) * (a*d) * (-b + c)^2 := by positivity
    have hs4 : 0 ≤ (1 : ℝ) * (a*c) * (-b + d)^2 := by positivity
    have hs5 : 0 ≤ (1 : ℝ) * (a*b) * (-c + d)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5]
  have hd : (0 : ℝ) < (a*b*c*d*(a + b + c + d)) := by positivity
  have heqrat : ( (1 / a + 1 / b + 1 / c + 1 / d) ) - ( 16 / (a + b + c + d)  ) = (a^2*b*c + a^2*b*d + a^2*c*d + a*b^2*c + a*b^2*d + a*b*c^2 - 12*a*b*c*d + a*b*d^2 + a*c^2*d + a*c*d^2 + b^2*c*d + b*c^2*d + b*c*d^2) / (a*b*c*d*(a + b + c + d)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (1 / a + 1 / b + 1 / c + 1 / d) ≥ 16 / (a + b + c + d)) := @solution
#print axioms solution
