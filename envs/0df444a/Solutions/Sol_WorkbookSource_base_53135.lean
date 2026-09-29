-- Prove2me | solution 1 for WorkbookSource.base_53135
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:28:33.51317+00:00
-- url     : https://prove2.me/submissions/db8c8d2c-c817-41c2-b03b-8537cb1e0f16

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + 2 * b = 2) : (a^2 + 1) * (b^2 + 1) > 9 / 5  := by
  have helim : a = (2 - 2*b) := by linarith only [hab]
  have hsum : 0 < (441/61 : ℝ) * (-244*b^2/441 + b - 244/441)^2 + (788/441 : ℝ) * (b^2 - 17861/24034)^2 + (27/3665185 : ℝ) * (1)^2 := by positivity
  have hid : ( (a^2 + 1) * (b^2 + 1) ) - ( 9 / 5  ) = (441/61 : ℝ) * (-244*b^2/441 + b - 244/441)^2 + (788/441 : ℝ) * (b^2 - 17861/24034)^2 + (27/3665185 : ℝ) * (1)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + 2 * b = 2), (a^2 + 1) * (b^2 + 1) > 9 / 5) := @solution
#print axioms solution
