-- Prove2me | solution 1 for WorkbookSource.base_31081
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:59:51.800476+00:00
-- url     : https://prove2.me/submissions/c4f8698e-0313-4fcd-b9a7-936aef1a0984

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : 8 * (a + b + c) ^ 2 * (a * b + b * c + a * c) + 8 * (d + a + b) ^ 2 * (d * a + a * b + d * b) + 8 * (b + c + d) ^ 2 * (b * c + c * d + b * d) + 8 * (a + c + d) ^ 2 * (a * c + a * d + c * d) + 189 * a * b * c * d ≥ 13 * (a + c + d) * (d + a + b) * (a + b + c) * (b + c + d)  := by
  have hn : 0 ≤ (3*a^3*b + 3*a^3*c + 3*a^3*d + 6*a^2*b^2 - 12*a^2*b*c - 12*a^2*b*d + 6*a^2*c^2 - 12*a^2*c*d + 6*a^2*d^2 + 3*a*b^3 - 12*a*b^2*c - 12*a*b^2*d - 12*a*b*c^2 + 72*a*b*c*d - 12*a*b*d^2 + 3*a*c^3 - 12*a*c^2*d - 12*a*c*d^2 + 3*a*d^3 + 3*b^3*c + 3*b^3*d + 6*b^2*c^2 - 12*b^2*c*d + 6*b^2*d^2 + 3*b*c^3 - 12*b*c^2*d - 12*b*c*d^2 + 3*b*d^3 + 3*c^3*d + 6*c^2*d^2 + 3*c*d^3) := by
    have hs0 : 0 ≤ (12 : ℝ) * (1) * (a*b - a*c/2 - a*d/2 - b*c/2 - b*d/2 + c*d)^2 := by positivity
    have hs1 : 0 ≤ (9 : ℝ) * (1) * (a*c - a*d - b*c + b*d)^2 := by positivity
    have hs2 : 0 ≤ (3 : ℝ) * (c*d) * (-c + d)^2 := by positivity
    have hs3 : 0 ≤ (3 : ℝ) * (b*d) * (-b + d)^2 := by positivity
    have hs4 : 0 ≤ (3 : ℝ) * (b*c) * (-b + c)^2 := by positivity
    have hs5 : 0 ≤ (3 : ℝ) * (a*d) * (-a + d)^2 := by positivity
    have hs6 : 0 ≤ (3 : ℝ) * (a*c) * (-a + c)^2 := by positivity
    have hs7 : 0 ≤ (3 : ℝ) * (a*b) * (-a + b)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7]
  have hd : (0 : ℝ) < (1) := by positivity
  have heqrat : ( 8 * (a + b + c) ^ 2 * (a * b + b * c + a * c) + 8 * (d + a + b) ^ 2 * (d * a + a * b + d * b) + 8 * (b + c + d) ^ 2 * (b * c + c * d + b * d) + 8 * (a + c + d) ^ 2 * (a * c + a * d + c * d) + 189 * a * b * c * d ) - ( 13 * (a + c + d) * (d + a + b) * (a + b + c) * (b + c + d)  ) = (3*a^3*b + 3*a^3*c + 3*a^3*d + 6*a^2*b^2 - 12*a^2*b*c - 12*a^2*b*d + 6*a^2*c^2 - 12*a^2*c*d + 6*a^2*d^2 + 3*a*b^3 - 12*a*b^2*c - 12*a*b^2*d - 12*a*b*c^2 + 72*a*b*c*d - 12*a*b*d^2 + 3*a*c^3 - 12*a*c^2*d - 12*a*c*d^2 + 3*a*d^3 + 3*b^3*c + 3*b^3*d + 6*b^2*c^2 - 12*b^2*c*d + 6*b^2*d^2 + 3*b*c^3 - 12*b*c^2*d - 12*b*c*d^2 + 3*b*d^3 + 3*c^3*d + 6*c^2*d^2 + 3*c*d^3) / (1) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), 8 * (a + b + c) ^ 2 * (a * b + b * c + a * c) + 8 * (d + a + b) ^ 2 * (d * a + a * b + d * b) + 8 * (b + c + d) ^ 2 * (b * c + c * d + b * d) + 8 * (a + c + d) ^ 2 * (a * c + a * d + c * d) + 189 * a * b * c * d ≥ 13 * (a + c + d) * (d + a + b) * (a + b + c) * (b + c + d)) := @solution
#print axioms solution
