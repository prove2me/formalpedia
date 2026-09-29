-- Prove2me | solution 1 for WorkbookSource.base_47415
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:49:55.95581+00:00
-- url     : https://prove2.me/submissions/00c57fac-4a0e-49a6-892a-16a62e609f26

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a)) * (b / (c + a) + c / (a + b)) * (c / (a + b) + a / (b + c)) ≥ 1 + 9 * (a - b) ^ 2 / (a + b) ^ 2 * (b - c) ^ 2 / (b + c) ^ 2 * (c - a) ^ 2 / (c + a) ^ 2  := by
  have hn : 0 ≤ (a^5*b + a^5*c - 8*a^4*b^2 + 18*a^4*b*c - 8*a^4*c^2 + 18*a^3*b^3 - 19*a^3*b^2*c - 19*a^3*b*c^2 + 18*a^3*c^3 - 8*a^2*b^4 - 19*a^2*b^3*c + 48*a^2*b^2*c^2 - 19*a^2*b*c^3 - 8*a^2*c^4 + a*b^5 + 18*a*b^4*c - 19*a*b^3*c^2 - 19*a*b^2*c^3 + 18*a*b*c^4 + a*c^5 + b^5*c - 8*b^4*c^2 + 18*b^3*c^3 - 8*b^2*c^4 + b*c^5) := by
    have hs0 : 0 ≤ (16 : ℝ) * (b*c) * (7*a^2/36 - 25*a*b/72 - 25*a*c/72 - b^2/4 + b*c - c^2/4)^2 := by positivity
    have hs1 : 0 ≤ (959/81 : ℝ) * (b*c) * (a^2 - a*b/2 - a*c/2)^2 := by positivity
    have hs2 : 0 ≤ (16 : ℝ) * (a*c) * (-a^2/4 - 25*a*b/72 + a*c + 7*b^2/36 - 25*b*c/72 - c^2/4)^2 := by positivity
    have hs3 : 0 ≤ (959/81 : ℝ) * (a*c) * (-a*b/2 + b^2 - b*c/2)^2 := by positivity
    have hs4 : 0 ≤ (16 : ℝ) * (a*b) * (-a^2/4 + a*b - 25*a*c/72 - b^2/4 - 25*b*c/72 + 7*c^2/36)^2 := by positivity
    have hs5 : 0 ≤ (959/81 : ℝ) * (a*b) * (-a*c/2 - b*c/2 + c^2)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5]
  have hd : (0 : ℝ) < ((a + b)^2*(a + c)^2*(b + c)^2) := by positivity
  have heqrat : ( (a / (b + c) + b / (c + a)) * (b / (c + a) + c / (a + b)) * (c / (a + b) + a / (b + c)) ) - ( 1 + 9 * (a - b) ^ 2 / (a + b) ^ 2 * (b - c) ^ 2 / (b + c) ^ 2 * (c - a) ^ 2 / (c + a) ^ 2  ) = (a^5*b + a^5*c - 8*a^4*b^2 + 18*a^4*b*c - 8*a^4*c^2 + 18*a^3*b^3 - 19*a^3*b^2*c - 19*a^3*b*c^2 + 18*a^3*c^3 - 8*a^2*b^4 - 19*a^2*b^3*c + 48*a^2*b^2*c^2 - 19*a^2*b*c^3 - 8*a^2*c^4 + a*b^5 + 18*a*b^4*c - 19*a*b^3*c^2 - 19*a*b^2*c^3 + 18*a*b*c^4 + a*c^5 + b^5*c - 8*b^4*c^2 + 18*b^3*c^3 - 8*b^2*c^4 + b*c^5) / ((a + b)^2*(a + c)^2*(b + c)^2) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (b + c) + b / (c + a)) * (b / (c + a) + c / (a + b)) * (c / (a + b) + a / (b + c)) ≥ 1 + 9 * (a - b) ^ 2 / (a + b) ^ 2 * (b - c) ^ 2 / (b + c) ^ 2 * (c - a) ^ 2 / (c + a) ^ 2) := @solution
#print axioms solution
