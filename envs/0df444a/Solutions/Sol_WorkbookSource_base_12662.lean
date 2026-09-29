-- Prove2me | solution 1 for WorkbookSource.base_12662
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:29.612234+00:00
-- url     : https://prove2.me/submissions/523ccfdb-45dd-4559-9089-eec6cf9d854a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (9 * a ^ 2 + 9 * b ^ 2 + c ^ 2) * (1 / (a + 4 * c) + 1 / (b + 4 * c)) ≥ 2 * (a + b)  := by
  have hn : 0 ≤ (9*a^3 + 7*a^2*b + 64*a^2*c + 7*a*b^2 - 16*a*b*c - 31*a*c^2 + 9*b^3 + 64*b^2*c - 31*b*c^2 + 8*c^3) := by
    have hs0 : 0 ≤ (70 : ℝ) * (c) * (-3*a/35 + b - 8*c/35)^2 := by positivity
    have hs1 : 0 ≤ (2432/35 : ℝ) * (c) * (a - c/4)^2 := by positivity
    have hs2 : 0 ≤ (9 : ℝ) * (b) * (a/3 + b - c/3)^2 := by positivity
    have hs3 : 0 ≤ (9 : ℝ) * (a) * (a + b/3 - c/3)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0), (9 * a ^ 2 + 9 * b ^ 2 + c ^ 2) * (1 / (a + 4 * c) + 1 / (b + 4 * c)) ≥ 2 * (a + b)) := @solution
#print axioms solution
