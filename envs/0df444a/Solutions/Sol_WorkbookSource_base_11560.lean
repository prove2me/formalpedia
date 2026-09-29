-- Prove2me | solution 1 for WorkbookSource.base_11560
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:12:15.705182+00:00
-- url     : https://prove2.me/submissions/623d6762-93d5-4526-8720-9dc32e12fa36

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (habc : a + b + c = 0) : a^2 * b^2 + a^2 * c^2 + b^2 * c^2 + 3 ≥ 6 * a * b * c  := by
  have helim0 : c = (-a - b) := by
    have hh := habc
    linarith only [hh]
  have hsum : 0 ≤ (3 : ℝ) * (1) * (-a^2/3 - a*b/3 - b^2/3 + 1)^2 + (8/3 : ℝ) * (1) * (a^2/4 + a*b + 3*a/4 + b^2/4 + 3*b/4)^2 + (1/2 : ℝ) * (1) * (a^2 - a - b^2 + b)^2 := by positivity
  have hid : ( a^2 * b^2 + a^2 * c^2 + b^2 * c^2 + 3 ) - ( 6 * a * b * c  ) = (3 : ℝ) * (1) * (-a^2/3 - a*b/3 - b^2/3 + 1)^2 + (8/3 : ℝ) * (1) * (a^2/4 + a*b + 3*a/4 + b^2/4 + 3*b/4)^2 + (1/2 : ℝ) * (1) * (a^2 - a - b^2 + b)^2 := by
    try simp only [helim0]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (habc : a + b + c = 0), a^2 * b^2 + a^2 * c^2 + b^2 * c^2 + 3 ≥ 6 * a * b * c) := @solution
#print axioms solution
