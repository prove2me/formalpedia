-- Prove2me | solution 1 for WorkbookSource.base_29587
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:45:33.534379+00:00
-- url     : https://prove2.me/submissions/8a4aa1ca-6427-49ea-abed-f94d4e513cf8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (2 / (a + b + c + d) - 1 / (a * b + b * c + c * d + d * a)) ≤ 1 / 4  := by
  have hn : 0 ≤ (a^2*b + a^2*d + a*b^2 + 2*a*b*c + 2*a*b*d - 8*a*b + 2*a*c*d + a*d^2 - 8*a*d + 4*a + b^2*c + b*c^2 + 2*b*c*d - 8*b*c + 4*b + c^2*d + c*d^2 - 8*c*d + 4*c + 4*d) := by
    have hs0 : 0 ≤ (4 : ℝ) * (d) * (-a/2 - c/2 + 1)^2 := by positivity
    have hs1 : 0 ≤ (4 : ℝ) * (c) * (-b/2 - d/2 + 1)^2 := by positivity
    have hs2 : 0 ≤ (4 : ℝ) * (b) * (-a/2 - c/2 + 1)^2 := by positivity
    have hs3 : 0 ≤ (4 : ℝ) * (a) * (-b/2 - d/2 + 1)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3]
  have hd : (0 : ℝ) < (4*(a + c)*(b + d)*(a + b + c + d)) := by positivity
  have heqrat : ( 1 / 4  ) - ( (2 / (a + b + c + d) - 1 / (a * b + b * c + c * d + d * a)) ) = (a^2*b + a^2*d + a*b^2 + 2*a*b*c + 2*a*b*d - 8*a*b + 2*a*c*d + a*d^2 - 8*a*d + 4*a + b^2*c + b*c^2 + 2*b*c*d - 8*b*c + 4*b + c^2*d + c*d^2 - 8*c*d + 4*c + 4*d) / (4*(a + c)*(b + d)*(a + b + c + d)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (2 / (a + b + c + d) - 1 / (a * b + b * c + c * d + d * a)) ≤ 1 / 4) := @solution
#print axioms solution
