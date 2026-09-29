-- Prove2me | solution 1 for WorkbookSource.base_14529
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:59:50.078812+00:00
-- url     : https://prove2.me/submissions/f9e05983-d4a2-479c-ada7-1f62353abe41

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 4) : a^2 + b^2 + c^3 ≥ 11 / 2  := by
  have hhom : 0 ≤ (21*a^3/64 - a^2*b/64 - a^2*c/64 - a*b^2/64 - 33*a*b*c/32 - 33*a*c^2/64 + 21*b^3/64 - b^2*c/64 - 33*b*c^2/64 + 117*c^3/64) := by
    have hs0 : 0 ≤ (117/64 : ℝ) * (c) * (-a/3 - b/3 + c)^2 := by positivity
    have hs1 : 0 ≤ (45/64 : ℝ) * (b) * (-23*a/45 - 7*b/45 + c)^2 := by positivity
    have hs2 : 0 ≤ (14/45 : ℝ) * (b) * (-a + b)^2 := by positivity
    have hs3 : 0 ≤ (45/64 : ℝ) * (a) * (-7*a/45 - 23*b/45 + c)^2 := by positivity
    have hs4 : 0 ≤ (14/45 : ℝ) * (a) * (-a + b)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4]
  have hehom : (2*a^2 + 2*b^2 + 2*c^3 - 11) = (21*a^3/64 - a^2*b/64 - a^2*c/64 - a*b^2/64 - 33*a*b*c/32 - 33*a*c^2/64 + 21*b^3/64 - b^2*c/64 - 33*b*c^2/64 + 117*c^3/64) := by
    linear_combination (-21*a^2/64 + 11*a*b/32 + 11*a*c/32 + 11*a/16 - 21*b^2/64 + 11*b*c/32 + 11*b/16 + 11*c^2/64 + 11*c/16 + 11/4) * habc
  have hn : 0 ≤ (2*a^2 + 2*b^2 + 2*c^3 - 11) := by linarith only [hhom, hehom]
  have hd : (0 : ℝ) < (2) := by positivity
  have heqrat : ( a^2 + b^2 + c^3 ) - ( 11 / 2  ) = (2*a^2 + 2*b^2 + 2*c^3 - 11) / (2) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 4), a^2 + b^2 + c^3 ≥ 11 / 2) := @solution
#print axioms solution
