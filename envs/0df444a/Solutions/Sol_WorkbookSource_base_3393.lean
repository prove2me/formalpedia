-- Prove2me | solution 1 for WorkbookSource.base_3393
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:28:28.622583+00:00
-- url     : https://prove2.me/submissions/36964de2-9b47-4092-8fbf-5c1d6e4c273f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : a^2 + b^2 ≤ 7 / 16 + a^5 + b^5  := by
  have helim : b = (1 - a) := by linarith only [hab]
  have hsum : 0 ≤ (11/2 : ℝ) * (-10*a^2/11 + a - 3/11)^2 + (5/11 : ℝ) * (a^2 - 1/4)^2 := by positivity
  have hid : ( 7 / 16 + a^5 + b^5  ) - ( a^2 + b^2 ) = (11/2 : ℝ) * (-10*a^2/11 + a - 3/11)^2 + (5/11 : ℝ) * (a^2 - 1/4)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1), a^2 + b^2 ≤ 7 / 16 + a^5 + b^5) := @solution
#print axioms solution
