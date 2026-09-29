-- Prove2me | solution 1 for WorkbookSource.base_7880
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:45:31.387519+00:00
-- url     : https://prove2.me/submissions/34024290-031f-44bf-8810-7741cdce7ab7

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (c + d + 4 * a) / (a + b) + (d + a + 4 * b) / (b + c) + (a + b + 4 * c) / (c + d) + (b + c + 4 * d) / (d + a) ≥ 12  := by
  have hn : 0 ≤ (a^3*b + 2*a^3*c + a^3*d + 2*a^2*b^2 + 3*a^2*b*c - 2*a^2*b*d - 4*a^2*c^2 - 5*a^2*c*d + 2*a^2*d^2 + a*b^3 - 2*a*b^2*c - 5*a*b^2*d - 5*a*b*c^2 + 3*a*b*d^2 + 2*a*c^3 + 3*a*c^2*d - 2*a*c*d^2 + a*d^3 + b^3*c + 2*b^3*d + 2*b^2*c^2 + 3*b^2*c*d - 4*b^2*d^2 + b*c^3 - 2*b*c^2*d - 5*b*c*d^2 + 2*b*d^3 + c^3*d + 2*c^2*d^2 + c*d^3) := by
    have hs0 : 0 ≤ (1 : ℝ) * (c*d) * (-a - b + c + d)^2 := by positivity
    have hs1 : 0 ≤ (2 : ℝ) * (b*d) * (a - b - c + d)^2 := by positivity
    have hs2 : 0 ≤ (1 : ℝ) * (b*c) * (a - b - c + d)^2 := by positivity
    have hs3 : 0 ≤ (1 : ℝ) * (a*d) * (a - b - c + d)^2 := by positivity
    have hs4 : 0 ≤ (2 : ℝ) * (a*c) * (-a - b + c + d)^2 := by positivity
    have hs5 : 0 ≤ (1 : ℝ) * (a*b) * (-a - b + c + d)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5]
  have hd : 0 < ((a + b)*(a + d)*(b + c)*(c + d)) := by positivity
  have heqrat : ( (c + d + 4 * a) / (a + b) + (d + a + 4 * b) / (b + c) + (a + b + 4 * c) / (c + d) + (b + c + 4 * d) / (d + a) ) - ( 12  ) = (a^3*b + 2*a^3*c + a^3*d + 2*a^2*b^2 + 3*a^2*b*c - 2*a^2*b*d - 4*a^2*c^2 - 5*a^2*c*d + 2*a^2*d^2 + a*b^3 - 2*a*b^2*c - 5*a*b^2*d - 5*a*b*c^2 + 3*a*b*d^2 + 2*a*c^3 + 3*a*c^2*d - 2*a*c*d^2 + a*d^3 + b^3*c + 2*b^3*d + 2*b^2*c^2 + 3*b^2*c*d - 4*b^2*d^2 + b*c^3 - 2*b*c^2*d - 5*b*c*d^2 + 2*b*d^3 + c^3*d + 2*c^2*d^2 + c*d^3) / ((a + b)*(a + d)*(b + c)*(c + d)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (c + d + 4 * a) / (a + b) + (d + a + 4 * b) / (b + c) + (a + b + 4 * c) / (c + d) + (b + c + 4 * d) / (d + a) ≥ 12) := @solution
#print axioms solution
