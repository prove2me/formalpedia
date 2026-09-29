-- Prove2me | solution 1 for WorkbookSource.plus_21539
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:53:29.043733+00:00
-- url     : https://prove2.me/submissions/8c45f753-a548-47a4-95f1-74644ea3e5b7

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (1 + 2 * a / (b + c)) * (1 + 2 * b / (c + d)) * (1 + 2 * c / (d + a)) * (1 + 2 * d / (a + b)) ≥ 9   := by
  have hn : 0 ≤ (4*a^3*b + 2*a^3*c + 2*a^3*d + 6*a^2*b^2 + 4*a^2*b*c + 6*a^2*b*d - 4*a^2*c^2 + 2*a^2*c*d + 6*a^2*d^2 + 2*a*b^3 + 6*a*b^2*c + 2*a*b^2*d + 2*a*b*c^2 + 16*a*b*c*d + 4*a*b*d^2 + 2*a*c^3 + 4*a*c^2*d + 6*a*c*d^2 + 4*a*d^3 + 4*b^3*c + 2*b^3*d + 6*b^2*c^2 + 4*b^2*c*d - 4*b^2*d^2 + 2*b*c^3 + 6*b*c^2*d + 2*b*c*d^2 + 2*b*d^3 + 4*c^3*d + 6*c^2*d^2 + 2*c*d^3) := by
    have hs0 : 0 ≤ (11/5 : ℝ) * (1) * (131*a*b/132 + 4*a*d/11 + 4*b*c/11 + c*d)^2 := by positivity
    have hs1 : 0 ≤ (21/11 : ℝ) * (1) * (a*b/315 + a*d + b*c)^2 := by positivity
    have hs2 : 0 ≤ (2509/75600 : ℝ) * (1) * (a*b)^2 := by positivity
    have hs3 : 0 ≤ (4 : ℝ) * (c*d) * (19*a/48 + 221*b/560 + c + 19*d/40)^2 := by positivity
    have hs4 : 0 ≤ (439/400 : ℝ) * (c*d) * (-3035*a/18438 - 999*b/6146 + d)^2 := by positivity
    have hs5 : 0 ≤ (77699/387198 : ℝ) * (c*d) * (a + 69354*b/77699)^2 := by positivity
    have hs6 : 0 ≤ (245390/11421753 : ℝ) * (c*d) * (b)^2 := by positivity
    have hs7 : 0 ≤ (2 : ℝ) * (b*d) * (-b + d)^2 := by positivity
    have hs8 : 0 ≤ (1/10 : ℝ) * (b*d) * (a + c)^2 := by positivity
    have hs9 : 0 ≤ (4 : ℝ) * (b*c) * (221*a/560 + b + 19*c/40 + 19*d/48)^2 := by positivity
    have hs10 : 0 ≤ (439/400 : ℝ) * (b*c) * (-999*a/6146 + c - 3035*d/18438)^2 := by positivity
    have hs11 : 0 ≤ (77699/387198 : ℝ) * (b*c) * (69354*a/77699 + d)^2 := by positivity
    have hs12 : 0 ≤ (245390/11421753 : ℝ) * (b*c) * (a)^2 := by positivity
    have hs13 : 0 ≤ (4 : ℝ) * (a*d) * (19*a/40 + 19*b/48 + 221*c/560 + d)^2 := by positivity
    have hs14 : 0 ≤ (439/400 : ℝ) * (a*d) * (a - 3035*b/18438 - 999*c/6146)^2 := by positivity
    have hs15 : 0 ≤ (77699/387198 : ℝ) * (a*d) * (b + 69354*c/77699)^2 := by positivity
    have hs16 : 0 ≤ (245390/11421753 : ℝ) * (a*d) * (c)^2 := by positivity
    have hs17 : 0 ≤ (2 : ℝ) * (a*c) * (-a + c)^2 := by positivity
    have hs18 : 0 ≤ (1/10 : ℝ) * (a*c) * (b + d)^2 := by positivity
    have hs19 : 0 ≤ (4 : ℝ) * (a*b) * (a + 19*b/40 + 19*c/48 + 221*d/560)^2 := by positivity
    have hs20 : 0 ≤ (439/400 : ℝ) * (a*b) * (b - 3035*c/18438 - 999*d/6146)^2 := by positivity
    have hs21 : 0 ≤ (77699/387198 : ℝ) * (a*b) * (c + 69354*d/77699)^2 := by positivity
    have hs22 : 0 ≤ (245390/11421753 : ℝ) * (a*b) * (d)^2 := by positivity
    have hs23 : 0 ≤ (1/6 : ℝ) * (a*b*c*d) * (1)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23]
  have hd : (0 : ℝ) < ((a + b)*(a + d)*(b + c)*(c + d)) := by positivity
  have heqrat : ( (1 + 2 * a / (b + c)) * (1 + 2 * b / (c + d)) * (1 + 2 * c / (d + a)) * (1 + 2 * d / (a + b)) ) - ( 9   ) = (4*a^3*b + 2*a^3*c + 2*a^3*d + 6*a^2*b^2 + 4*a^2*b*c + 6*a^2*b*d - 4*a^2*c^2 + 2*a^2*c*d + 6*a^2*d^2 + 2*a*b^3 + 6*a*b^2*c + 2*a*b^2*d + 2*a*b*c^2 + 16*a*b*c*d + 4*a*b*d^2 + 2*a*c^3 + 4*a*c^2*d + 6*a*c*d^2 + 4*a*d^3 + 4*b^3*c + 2*b^3*d + 6*b^2*c^2 + 4*b^2*c*d - 4*b^2*d^2 + 2*b*c^3 + 6*b*c^2*d + 2*b*c*d^2 + 2*b*d^3 + 4*c^3*d + 6*c^2*d^2 + 2*c*d^3) / ((a + b)*(a + d)*(b + c)*(c + d)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (1 + 2 * a / (b + c)) * (1 + 2 * b / (c + d)) * (1 + 2 * c / (d + a)) * (1 + 2 * d / (a + b)) ≥ 9) := @solution
#print axioms solution
