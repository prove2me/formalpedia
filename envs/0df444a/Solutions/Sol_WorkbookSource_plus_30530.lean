-- Prove2me | solution 1 for WorkbookSource.plus_30530
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:28:34.701383+00:00
-- url     : https://prove2.me/submissions/a2ddee87-895d-4564-aafc-b6f86bd87ea3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 3 / 4) : a^2 - a^3 + b^2 - b^3 ≤ 45 / 256   := by
  have helim : b = (3/4 - a) := by linarith only [hab]
  have hsum : 0 ≤ (1/4 : ℝ) * (a - 3/8)^2 := by positivity
  have hid : ( 45 / 256   ) - ( a^2 - a^3 + b^2 - b^3 ) = (1/4 : ℝ) * (a - 3/8)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 3 / 4), a^2 - a^3 + b^2 - b^3 ≤ 45 / 256) := @solution
#print axioms solution
