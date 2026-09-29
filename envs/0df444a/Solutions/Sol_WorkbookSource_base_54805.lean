-- Prove2me | solution 1 for WorkbookSource.base_54805
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:53:28.452684+00:00
-- url     : https://prove2.me/submissions/e649c541-1116-4052-85f8-2054f34591bf

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : 1 + 6 / (a * b + a * c + a * d + b * c + b * d + c * d) ≥ 8 / (a + b + c + d)  := by
  have hn : 0 ≤ (a^2*b + a^2*c + a^2*d + a*b^2 + 3*a*b*c + 3*a*b*d - 8*a*b + a*c^2 + 3*a*c*d - 8*a*c + a*d^2 - 8*a*d + 6*a + b^2*c + b^2*d + b*c^2 + 3*b*c*d - 8*b*c + b*d^2 - 8*b*d + 6*b + c^2*d + c*d^2 - 8*c*d + 6*c + 6*d) := by
    have hs0 : 0 ≤ (6 : ℝ) * (d) * (-a/3 - b/3 - c/3 + 1)^2 := by positivity
    have hs1 : 0 ≤ (1/3 : ℝ) * (d) * (-a/2 - b/2 + c)^2 := by positivity
    have hs2 : 0 ≤ (1/4 : ℝ) * (d) * (-a + b)^2 := by positivity
    have hs3 : 0 ≤ (6 : ℝ) * (c) * (-a/3 - b/3 - d/3 + 1)^2 := by positivity
    have hs4 : 0 ≤ (1/3 : ℝ) * (c) * (-a/2 - b/2 + d)^2 := by positivity
    have hs5 : 0 ≤ (1/4 : ℝ) * (c) * (-a + b)^2 := by positivity
    have hs6 : 0 ≤ (6 : ℝ) * (b) * (-a/3 - c/3 - d/3 + 1)^2 := by positivity
    have hs7 : 0 ≤ (1/3 : ℝ) * (b) * (-a/2 - c/2 + d)^2 := by positivity
    have hs8 : 0 ≤ (1/4 : ℝ) * (b) * (-a + c)^2 := by positivity
    have hs9 : 0 ≤ (6 : ℝ) * (a) * (-b/3 - c/3 - d/3 + 1)^2 := by positivity
    have hs10 : 0 ≤ (1/3 : ℝ) * (a) * (-b/2 - c/2 + d)^2 := by positivity
    have hs11 : 0 ≤ (1/4 : ℝ) * (a) * (-b + c)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11]
  have hd : (0 : ℝ) < ((a + b + c + d)*(a*b + a*c + a*d + b*c + b*d + c*d)) := by positivity
  have heqrat : ( 1 + 6 / (a * b + a * c + a * d + b * c + b * d + c * d) ) - ( 8 / (a + b + c + d)  ) = (a^2*b + a^2*c + a^2*d + a*b^2 + 3*a*b*c + 3*a*b*d - 8*a*b + a*c^2 + 3*a*c*d - 8*a*c + a*d^2 - 8*a*d + 6*a + b^2*c + b^2*d + b*c^2 + 3*b*c*d - 8*b*c + b*d^2 - 8*b*d + 6*b + c^2*d + c*d^2 - 8*c*d + 6*c + 6*d) / ((a + b + c + d)*(a*b + a*c + a*d + b*c + b*d + c*d)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), 1 + 6 / (a * b + a * c + a * d + b * c + b * d + c * d) ≥ 8 / (a + b + c + d)) := @solution
#print axioms solution
