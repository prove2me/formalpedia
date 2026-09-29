-- Prove2me | solution 1 for WorkbookSource.base_2528
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:55.400847+00:00
-- url     : https://prove2.me/submissions/8a124f0e-e3c1-4c83-b825-58af71aea35b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a + b) ^ 2 / c + c ^ 2 / a ≥ 4 * b  := by
  have hn : 0 ≤ (a^3 + 2*a^2*b + a*b^2 - 4*a*b*c + c^3) := by
    have hs0 : 0 ≤ (4 : ℝ) * (c) * (a - c/2)^2 := by positivity
    have hs1 : 0 ≤ (4 : ℝ) * (a) * (-a/2 - b/2 + c)^2 := by positivity
    nlinarith only [hs0, hs1]
  have hd : 0 < (a*c : ℝ) := by positivity
  have he : ( (a + b) ^ 2 / c + c ^ 2 / a ) - ( 4 * b  ) = (a^3 + 2*a^2*b + a*b^2 - 4*a*b*c + c^3) / (a*c) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  rw [← he] at hp
  linarith only [hp]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0), (a + b) ^ 2 / c + c ^ 2 / a ≥ 4 * b) := @solution
#print axioms solution
