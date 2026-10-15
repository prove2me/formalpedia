-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T08:34:49.471684+00:00
-- url     : https://prove2.me/submissions/ad055b11-6822-4826-82c8-f0e9b2dc63fc

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterValuesLeft
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 RHHighVerticalCenterLeft.coefficients=RHHighVerticalCenterValuesLeft.values ∧ RHHighVerticalCenterValuesLeft.values.length=55 := by decide +kernel
