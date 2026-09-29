-- Prove2me | solution 1 for WorkbookSource.base_21324
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:45:34.711996+00:00
-- url     : https://prove2.me/submissions/3e8dde65-c532-499c-ba47-8b29a95d7aa2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b + c = 3) : 10 * (a ^ 2 + b ^ 2 + c ^ 2) - 8 * (1 / a + 1 / b + 1 / c) ≤ 9  := by
  have hhom : 0 ≤ (8*a^4*b/27 + 8*a^4*c/27 + 8*a^3*b^2/9 - 187*a^3*b*c/27 + 8*a^3*c^2/9 + 8*a^2*b^3/9 + 50*a^2*b^2*c/9 + 50*a^2*b*c^2/9 + 8*a^2*c^3/9 + 8*a*b^4/27 - 187*a*b^3*c/27 + 50*a*b^2*c^2/9 - 187*a*b*c^3/27 + 8*a*c^4/27 + 8*b^4*c/27 + 8*b^3*c^2/9 + 8*b^2*c^3/9 + 8*b*c^4/27) := by
    have hs0 : 0 ≤ (49/9 : ℝ) * (c) * (-3*a^2/14 + a*b - a*c/14 - 3*b^2/14 - b*c/14)^2 := by positivity
    have hs1 : 0 ≤ (125/108 : ℝ) * (c) * (a^2/5 - a*c - b^2/5 + b*c)^2 := by positivity
    have hs2 : 0 ≤ (49/9 : ℝ) * (b) * (-3*a^2/14 - a*b/14 + a*c - b*c/14 - 3*c^2/14)^2 := by positivity
    have hs3 : 0 ≤ (125/108 : ℝ) * (b) * (a^2/5 - a*b + b*c - c^2/5)^2 := by positivity
    have hs4 : 0 ≤ (49/9 : ℝ) * (a) * (-a*b/14 - a*c/14 - 3*b^2/14 + b*c - 3*c^2/14)^2 := by positivity
    have hs5 : 0 ≤ (125/108 : ℝ) * (a) * (-a*b + a*c + b^2/5 - c^2/5)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5]
  have hehom : (-10*a^3*b*c - 10*a*b^3*c - 10*a*b*c^3 + 9*a*b*c + 8*a*b + 8*a*c + 8*b*c) = (8*a^4*b/27 + 8*a^4*c/27 + 8*a^3*b^2/9 - 187*a^3*b*c/27 + 8*a^3*c^2/9 + 8*a^2*b^3/9 + 50*a^2*b^2*c/9 + 50*a^2*b*c^2/9 + 8*a^2*c^3/9 + 8*a*b^4/27 - 187*a*b^3*c/27 + 50*a*b^2*c^2/9 - 187*a*b*c^3/27 + 8*a*c^4/27 + 8*b^4*c/27 + 8*b^3*c^2/9 + 8*b^2*c^3/9 + 8*b*c^4/27) := by
    linear_combination (-8*a^3*b/27 - 8*a^3*c/27 - 16*a^2*b^2/27 - 67*a^2*b*c/27 - 8*a^2*b/9 - 16*a^2*c^2/27 - 8*a^2*c/9 - 8*a*b^3/27 - 67*a*b^2*c/27 - 8*a*b^2/9 - 67*a*b*c^2/27 - 17*a*b*c/3 - 8*a*b/3 - 8*a*c^3/27 - 8*a*c^2/9 - 8*a*c/3 - 8*b^3*c/27 - 16*b^2*c^2/27 - 8*b^2*c/9 - 8*b*c^3/27 - 8*b*c^2/9 - 8*b*c/3) * hab
  have hn : 0 ≤ (-10*a^3*b*c - 10*a*b^3*c - 10*a*b*c^3 + 9*a*b*c + 8*a*b + 8*a*c + 8*b*c) := by linarith only [hhom, hehom]
  have hd : 0 < (a*b*c) := by positivity
  have heqrat : ( 9  ) - ( 10 * (a ^ 2 + b ^ 2 + c ^ 2) - 8 * (1 / a + 1 / b + 1 / c) ) = (-10*a^3*b*c - 10*a*b^3*c - 10*a*b*c^3 + 9*a*b*c + 8*a*b + 8*a*c + 8*b*c) / (a*b*c) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b + c = 3), 10 * (a ^ 2 + b ^ 2 + c ^ 2) - 8 * (1 / a + 1 / b + 1 / c) ≤ 9) := @solution
#print axioms solution
