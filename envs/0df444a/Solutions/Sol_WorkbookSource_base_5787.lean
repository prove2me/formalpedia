-- Prove2me | solution 1 for WorkbookSource.base_5787
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:44:23.813858+00:00
-- url     : https://prove2.me/submissions/35ab1cd1-7a08-4da1-9c04-6687df694f02

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x + 2/y) * (y/x + 2) ≥ 8  := by
  have hn : 0 ≤ (2*x^2*y + x*y^2 - 8*x*y + 4*x + 2*y) := by
    have hs0 : 0 ≤ (2 : ℝ) * (y) * (1 - x)^2 := by positivity
    have hs1 : 0 ≤ (4 : ℝ) * (x) * (1 - y/2)^2 := by positivity
    nlinarith only [hs0, hs1]
  field_simp (disch := positivity)
  nlinarith only [hn]

example : (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), (x + 2/y) * (y/x + 2) ≥ 8) := @solution
#print axioms solution
