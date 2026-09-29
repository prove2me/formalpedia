-- Prove2me | solution 1 for WorkbookSource.base_7716
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:37.42539+00:00
-- url     : https://prove2.me/submissions/ff6ed898-4e88-4dc9-929e-f77ceea9c58e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) ^ 2 + (a + b + 4 * c) ^ 2 ≥ 100 * a * b * c / (a + b + c)  := by
  have hn : 0 ≤ (2*a^3 + 6*a^2*b + 10*a^2*c + 6*a*b^2 - 80*a*b*c + 24*a*c^2 + 2*b^3 + 10*b^2*c + 24*b*c^2 + 16*c^3) := by
    have hs0 : 0 ≤ (16 : ℝ) * (c) * (-a/4 - b/4 + c)^2 := by positivity
    have hs1 : 0 ≤ (32 : ℝ) * (b) * (-41*a/64 + 9*b/64 + c)^2 := by positivity
    have hs2 : 0 ≤ (175/128 : ℝ) * (b) * (-a + b)^2 := by positivity
    have hs3 : 0 ≤ (32 : ℝ) * (a) * (9*a/64 - 41*b/64 + c)^2 := by positivity
    have hs4 : 0 ≤ (175/128 : ℝ) * (a) * (-a + b)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4]
  field_simp (disch := positivity)
  nlinarith only [hn]

example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) ^ 2 + (a + b + 4 * c) ^ 2 ≥ 100 * a * b * c / (a + b + c)) := @solution
#print axioms solution
