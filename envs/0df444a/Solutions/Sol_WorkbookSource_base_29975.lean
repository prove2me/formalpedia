-- Prove2me | solution 1 for WorkbookSource.base_29975
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:45:30.088841+00:00
-- url     : https://prove2.me/submissions/898ab20f-669a-4a58-975e-053d1bcabcdb

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 1 / (a ^ 2 + b ^ 2) + 7 / (a ^ 2 + 49 * b ^ 2) ≤ 2 / (3 * a * b)  := by
  have hn : 0 ≤ (2*(a^2 - 6*a*b + 7*b^2)^2) := by
    have hs0 : 0 ≤ (98 : ℝ) * (1) * (a^2/7 - 6*a*b/7 + b^2)^2 := by positivity
    nlinarith only [hs0]
  have hd : (0 : ℝ) < (3*a*b*(a^2 + b^2)*(a^2 + 49*b^2)) := by positivity
  have heqrat : ( 2 / (3 * a * b)  ) - ( 1 / (a ^ 2 + b ^ 2) + 7 / (a ^ 2 + 49 * b ^ 2) ) = (2*(a^2 - 6*a*b + 7*b^2)^2) / (3*a*b*(a^2 + b^2)*(a^2 + 49*b^2)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b), 1 / (a ^ 2 + b ^ 2) + 7 / (a ^ 2 + 49 * b ^ 2) ≤ 2 / (3 * a * b)) := @solution
#print axioms solution
