-- Prove2me | solution 1 for WorkbookSource.base_52622
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:50:00.784859+00:00
-- url     : https://prove2.me/submissions/fb605a52-56fc-4660-9c44-cde55338bb23

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a / (a + b) + c / (c + d) + a / (b + c) + 2 * b / (c + d) + c / (d + a) + 2 * d / (a + b)) ≥ 4  := by
  have hn : 0 ≤ (a^3*c + a^3*d + 2*a^2*b^2 + a^2*b*c - 2*a^2*b*d - 2*a^2*c^2 - 2*a^2*c*d + a^2*d^2 + 2*a*b^3 - a*b^2*c - 2*a*b^2*d - 2*a*b*c^2 + a*c^3 + a*c^2*d - a*c*d^2 + 2*b^3*d + b^2*c^2 - 4*b^2*d^2 + b*c^3 - 2*b*c^2*d - 2*b*c*d^2 + 2*b*d^3 + 2*c^2*d^2 + 2*c*d^3) := by
    have hs0 : 0 ≤ (2 : ℝ) * (1) * (-a*b/8 - a*d/4 - 5*b*c/8 + c*d)^2 := by positivity
    have hs1 : 0 ≤ (63/32 : ℝ) * (1) * (a*b - 2*a*d/3 - b*c/3)^2 := by positivity
    have hs2 : 0 ≤ (2 : ℝ) * (c*d) * (-b + d)^2 := by positivity
    have hs3 : 0 ≤ (2 : ℝ) * (b*d) * (-a/2 - b + c/2 + d)^2 := by positivity
    have hs4 : 0 ≤ (1 : ℝ) * (b*c) * (-a + c)^2 := by positivity
    have hs5 : 0 ≤ (1 : ℝ) * (a*d) * (-a + c)^2 := by positivity
    have hs6 : 0 ≤ (1 : ℝ) * (a*c) * (-a + c)^2 := by positivity
    have hs7 : 0 ≤ (2 : ℝ) * (a*b) * (-b + d)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7]
  have hd : (0 : ℝ) < ((a + b)*(a + d)*(b + c)*(c + d)) := by positivity
  have heqrat : ( (a / (a + b) + c / (c + d) + a / (b + c) + 2 * b / (c + d) + c / (d + a) + 2 * d / (a + b)) ) - ( 4  ) = (a^3*c + a^3*d + 2*a^2*b^2 + a^2*b*c - 2*a^2*b*d - 2*a^2*c^2 - 2*a^2*c*d + a^2*d^2 + 2*a*b^3 - a*b^2*c - 2*a*b^2*d - 2*a*b*c^2 + a*c^3 + a*c^2*d - a*c*d^2 + 2*b^3*d + b^2*c^2 - 4*b^2*d^2 + b*c^3 - 2*b*c^2*d - 2*b*c*d^2 + 2*b*d^3 + 2*c^2*d^2 + 2*c*d^3) / ((a + b)*(a + d)*(b + c)*(c + d)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (a / (a + b) + c / (c + d) + a / (b + c) + 2 * b / (c + d) + c / (d + a) + 2 * d / (a + b)) ≥ 4) := @solution
#print axioms solution
