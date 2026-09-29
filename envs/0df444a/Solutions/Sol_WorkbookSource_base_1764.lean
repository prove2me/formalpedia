-- Prove2me | solution 1 for WorkbookSource.base_1764
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:41:38.679639+00:00
-- url     : https://prove2.me/submissions/8c71501a-d711-4697-b2b1-dcd29f50585c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a + 3 * b) / (b + c) + (b + 3 * c) / (c + d) + (c + 3 * d) / (d + a) + (d + 3 * a) / (a + b) ≥ 8  := by
  have hn : 0 ≤ (a^3*c + a^3*d + a^2*b^2 + 3*a^2*b*c - a^2*b*d - 2*a^2*c^2 - 4*a^2*c*d + a^2*d^2 + a*b^3 - a*b^2*c - 4*a*b^2*d - 4*a*b*c^2 + 3*a*b*d^2 + a*c^3 + 3*a*c^2*d - a*c*d^2 + b^3*d + b^2*c^2 + 3*b^2*c*d - 2*b^2*d^2 + b*c^3 - b*c^2*d - 4*b*c*d^2 + b*d^3 + c^2*d^2 + c*d^3) := by
    have hs0 : 0 ≤ (1 : ℝ) * (1) * (a*b - a*d - b*c + c*d)^2 := by positivity
    have hs1 : 0 ≤ (1 : ℝ) * (c*d) * (-b + d)^2 := by positivity
    have hs2 : 0 ≤ (1 : ℝ) * (b*d) * (a - b - c + d)^2 := by positivity
    have hs3 : 0 ≤ (1 : ℝ) * (b*c) * (-a + c)^2 := by positivity
    have hs4 : 0 ≤ (1 : ℝ) * (a*d) * (-a + c)^2 := by positivity
    have hs5 : 0 ≤ (1 : ℝ) * (a*c) * (-a - b + c + d)^2 := by positivity
    have hs6 : 0 ≤ (1 : ℝ) * (a*b) * (-b + d)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5, hs6]
  have hd : 0 < ((a + b)*(a + d)*(b + c)*(c + d)) := by positivity
  have heqrat : ( (a + 3 * b) / (b + c) + (b + 3 * c) / (c + d) + (c + 3 * d) / (d + a) + (d + 3 * a) / (a + b) ) - ( 8  ) = (a^3*c + a^3*d + a^2*b^2 + 3*a^2*b*c - a^2*b*d - 2*a^2*c^2 - 4*a^2*c*d + a^2*d^2 + a*b^3 - a*b^2*c - 4*a*b^2*d - 4*a*b*c^2 + 3*a*b*d^2 + a*c^3 + 3*a*c^2*d - a*c*d^2 + b^3*d + b^2*c^2 + 3*b^2*c*d - 2*b^2*d^2 + b*c^3 - b*c^2*d - 4*b*c*d^2 + b*d^3 + c^2*d^2 + c*d^3) / ((a + b)*(a + d)*(b + c)*(c + d)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (a + 3 * b) / (b + c) + (b + 3 * c) / (c + d) + (c + 3 * d) / (d + a) + (d + 3 * a) / (a + b) ≥ 8) := @solution
#print axioms solution
