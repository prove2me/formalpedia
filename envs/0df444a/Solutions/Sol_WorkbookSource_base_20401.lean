-- Prove2me | solution 1 for WorkbookSource.base_20401
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:45:32.899086+00:00
-- url     : https://prove2.me/submissions/4acc1d75-14f7-4fcb-963b-90876286ba6d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (1 / (a * b) + 1 / (c * d)) ≥ 8 / (a + b) / (c + d)  := by
  have hn : 0 ≤ (a^2*b*c + a^2*b*d + a*b^2*c + a*b^2*d - 8*a*b*c*d + a*c^2*d + a*c*d^2 + b*c^2*d + b*c*d^2) := by
    have hs0 : 0 ≤ (1 : ℝ) * (b*d) * (-a + c)^2 := by positivity
    have hs1 : 0 ≤ (1 : ℝ) * (b*c) * (-a + d)^2 := by positivity
    have hs2 : 0 ≤ (1 : ℝ) * (a*d) * (-b + c)^2 := by positivity
    have hs3 : 0 ≤ (1 : ℝ) * (a*c) * (-b + d)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3]
  have hd : (0 : ℝ) < (a*b*c*d*(a + b)*(c + d)) := by positivity
  have heqrat : ( (1 / (a * b) + 1 / (c * d)) ) - ( 8 / (a + b) / (c + d)  ) = (a^2*b*c + a^2*b*d + a*b^2*c + a*b^2*d - 8*a*b*c*d + a*c^2*d + a*c*d^2 + b*c^2*d + b*c*d^2) / (a*b*c*d*(a + b)*(c + d)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (1 / (a * b) + 1 / (c * d)) ≥ 8 / (a + b) / (c + d)) := @solution
#print axioms solution
