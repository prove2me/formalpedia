-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_vertical_center_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T19:35:26.024978+00:00
-- url     : https://prove2.me/submissions/bd4858bc-1805-41bd-81ad-26d451861ec5

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalCenterValuesLeft
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 RHBatch01VerticalCenterLeft.coefficients=RHBatch01VerticalCenterValuesLeft.values ∧ RHBatch01VerticalCenterValuesLeft.values.length=55 := by decide +kernel
#print axioms solution
