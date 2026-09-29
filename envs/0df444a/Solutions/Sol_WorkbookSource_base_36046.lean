-- Prove2me | solution 1 for WorkbookSource.base_36046
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:49:58.710149+00:00
-- url     : https://prove2.me/submissions/1eddb13b-6ef1-4e07-b29c-ec5d75e29395

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (9 / 16) * (a + b + c + d) ^ 2 + (3 * (a * b * c + b * c * d + c * d * a + d * a * b)) / (a + b + c + d) ≥ 2 * (a * b + a * c + a * d + b * c + b * d + c * d)  := by
  have hn : 0 ≤ (9*a^3 - 5*a^2*b - 5*a^2*c - 5*a^2*d - 5*a*b^2 + 6*a*b*c + 6*a*b*d - 5*a*c^2 + 6*a*c*d - 5*a*d^2 + 9*b^3 - 5*b^2*c - 5*b^2*d - 5*b*c^2 + 6*b*c*d - 5*b*d^2 + 9*c^3 - 5*c^2*d - 5*c*d^2 + 9*d^3) := by
    have hs0 : 0 ≤ (9 : ℝ) * (d) * (-a/3 - b/3 - c/3 + d)^2 := by positivity
    have hs1 : 0 ≤ (9 : ℝ) * (c) * (-a/3 - b/3 + c - d/3)^2 := by positivity
    have hs2 : 0 ≤ (9 : ℝ) * (b) * (-a/3 + b - c/3 - d/3)^2 := by positivity
    have hs3 : 0 ≤ (9 : ℝ) * (a) * (a - b/3 - c/3 - d/3)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3]
  have hd : (0 : ℝ) < (16*a + 16*b + 16*c + 16*d) := by positivity
  have heqrat : ( (9 / 16) * (a + b + c + d) ^ 2 + (3 * (a * b * c + b * c * d + c * d * a + d * a * b)) / (a + b + c + d) ) - ( 2 * (a * b + a * c + a * d + b * c + b * d + c * d)  ) = (9*a^3 - 5*a^2*b - 5*a^2*c - 5*a^2*d - 5*a*b^2 + 6*a*b*c + 6*a*b*d - 5*a*c^2 + 6*a*c*d - 5*a*d^2 + 9*b^3 - 5*b^2*c - 5*b^2*d - 5*b*c^2 + 6*b*c*d - 5*b*d^2 + 9*c^3 - 5*c^2*d - 5*c*d^2 + 9*d^3) / (16*a + 16*b + 16*c + 16*d) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (9 / 16) * (a + b + c + d) ^ 2 + (3 * (a * b * c + b * c * d + c * d * a + d * a * b)) / (a + b + c + d) ≥ 2 * (a * b + a * c + a * d + b * c + b * d + c * d)) := @solution
#print axioms solution
