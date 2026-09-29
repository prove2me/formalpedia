-- Prove2me | solution 1 for WorkbookSource.base_40002
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:28:53.635091+00:00
-- url     : https://prove2.me/submissions/5cdd9ace-7644-4cdf-98a9-31b041494599

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (b c : ℝ) : (b^4 + 3) * (c^4 + 3) ≥ 3 * (b^2 + c^2)^2  := by
  have hsum : 0 ≤ (9 : ℝ) * (-b^2*c^2/3 + 1)^2 := by positivity
  have hid : ( (b^4 + 3) * (c^4 + 3) ) - ( 3 * (b^2 + c^2)^2  ) = (9 : ℝ) * (-b^2*c^2/3 + 1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (b c : ℝ), (b^4 + 3) * (c^4 + 3) ≥ 3 * (b^2 + c^2)^2) := @solution
#print axioms solution
