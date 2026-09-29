-- Prove2me | solution 1 for WorkbookSource.base_36763
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:49:59.350107+00:00
-- url     : https://prove2.me/submissions/f6b91a6b-c844-4fba-9f64-382488464e2f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : 3 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) + a * b * c * d * (1 / a + 1 / b + 1 / c + 1 / d) ≥ (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (a + b + c + d)  := by
  have hn : 0 ≤ (2*a^3 - a^2*b - a^2*c - a^2*d - a*b^2 + a*b*c + a*b*d - a*c^2 + a*c*d - a*d^2 + 2*b^3 - b^2*c - b^2*d - b*c^2 + b*c*d - b*d^2 + 2*c^3 - c^2*d - c*d^2 + 2*d^3) := by
    have hs0 : 0 ≤ (2 : ℝ) * (d) * (-a/3 - b/3 - c/3 + d)^2 := by positivity
    have hs1 : 0 ≤ (1/9 : ℝ) * (d) * (-a/2 - b/2 + c)^2 := by positivity
    have hs2 : 0 ≤ (1/12 : ℝ) * (d) * (-a + b)^2 := by positivity
    have hs3 : 0 ≤ (2 : ℝ) * (c) * (-a/3 - b/3 + c - d/3)^2 := by positivity
    have hs4 : 0 ≤ (1/9 : ℝ) * (c) * (-a/2 - b/2 + d)^2 := by positivity
    have hs5 : 0 ≤ (1/12 : ℝ) * (c) * (-a + b)^2 := by positivity
    have hs6 : 0 ≤ (2 : ℝ) * (b) * (-a/3 + b - c/3 - d/3)^2 := by positivity
    have hs7 : 0 ≤ (1/9 : ℝ) * (b) * (-a/2 - c/2 + d)^2 := by positivity
    have hs8 : 0 ≤ (1/12 : ℝ) * (b) * (-a + c)^2 := by positivity
    have hs9 : 0 ≤ (2 : ℝ) * (a) * (a - b/3 - c/3 - d/3)^2 := by positivity
    have hs10 : 0 ≤ (1/9 : ℝ) * (a) * (-b/2 - c/2 + d)^2 := by positivity
    have hs11 : 0 ≤ (1/12 : ℝ) * (a) * (-b + c)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11]
  have hd : (0 : ℝ) < (1) := by positivity
  have heqrat : ( 3 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) + a * b * c * d * (1 / a + 1 / b + 1 / c + 1 / d) ) - ( (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (a + b + c + d)  ) = (2*a^3 - a^2*b - a^2*c - a^2*d - a*b^2 + a*b*c + a*b*d - a*c^2 + a*c*d - a*d^2 + 2*b^3 - b^2*c - b^2*d - b*c^2 + b*c*d - b*d^2 + 2*c^3 - c^2*d - c*d^2 + 2*d^3) / (1) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), 3 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) + a * b * c * d * (1 / a + 1 / b + 1 / c + 1 / d) ≥ (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (a + b + c + d)) := @solution
#print axioms solution
