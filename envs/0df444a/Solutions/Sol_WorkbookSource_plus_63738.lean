-- Prove2me | solution 1 for WorkbookSource.plus_63738
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:28:35.335812+00:00
-- url     : https://prove2.me/submissions/4470016b-23ac-4e65-8bad-d5cffb8ea648

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (hab : a + b + c = 3) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a + 1) * (b + 1) * (c + 1) + (a * b * c - 1)^2 + (29 * (3 - a * b - b * c - a * c)) / 27   := by
  have helim : c = (-a - b + 3) := by linarith only [hab]
  have hsum : 0 ≤ (259/27 : ℝ) * (45*a^2/518 - 117*a*b/259 - 11*a/518 - 81*b^2/259 + b - 78/259)^2 + (89401/9324 : ℝ) * (-93*a^2/299 - 6*a*b/13 + a + 24*b^2/299 - 4/13)^2 := by positivity
  have hid : ( (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ) - ( (a + 1) * (b + 1) * (c + 1) + (a * b * c - 1)^2 + (29 * (3 - a * b - b * c - a * c)) / 27   ) = (259/27 : ℝ) * (45*a^2/518 - 117*a*b/259 - 11*a/518 - 81*b^2/259 + b - 78/259)^2 + (89401/9324 : ℝ) * (-93*a^2/299 - 6*a*b/13 + a + 24*b^2/299 - 4/13)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (hab : a + b + c = 3), (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a + 1) * (b + 1) * (c + 1) + (a * b * c - 1)^2 + (29 * (3 - a * b - b * c - a * c)) / 27) := @solution
#print axioms solution
