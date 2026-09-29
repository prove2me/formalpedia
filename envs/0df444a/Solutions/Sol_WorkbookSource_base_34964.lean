-- Prove2me | solution 1 for WorkbookSource.base_34964
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:46:58.368097+00:00
-- url     : https://prove2.me/submissions/bece2d6d-5875-4837-bee5-e8113deaa117

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (2 / a + 3 / (a + b)) ≤ 25 / 12 * (1 / a + 1 / b)  := by
  have hn : 0 ≤ ((5*a - b)^2) := by
    have hs0 : 0 ≤ (25 : ℝ) * (1) * (a - b/5)^2 := by positivity
    nlinarith only [hs0]
  have hd : (0 : ℝ) < (12*a*b*(a + b)) := by positivity
  have heqrat : ( 25 / 12 * (1 / a + 1 / b)  ) - ( (2 / a + 3 / (a + b)) ) = ((5*a - b)^2) / (12*a*b*(a + b)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b), (2 / a + 3 / (a + b)) ≤ 25 / 12 * (1 / a + 1 / b)) := @solution
#print axioms solution
