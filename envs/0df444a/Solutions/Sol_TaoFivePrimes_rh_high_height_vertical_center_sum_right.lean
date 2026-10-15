-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T08:45:01.902266+00:00
-- url     : https://prove2.me/submissions/5221ca2d-685e-4d1e-a5a3-ae53a84482b0

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterValuesRight
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 RHHighVerticalCenterRight.coefficients=RHHighVerticalCenterValuesRight.values ∧ RHHighVerticalCenterValuesRight.values.length=55 := by decide +kernel
