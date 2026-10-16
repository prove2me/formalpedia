-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_vertical_center_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T19:40:43.047284+00:00
-- url     : https://prove2.me/submissions/19cfb112-37ea-4be3-8412-052e2387816b

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01VerticalCenterValuesRight
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 RHBatch01VerticalCenterRight.coefficients=RHBatch01VerticalCenterValuesRight.values ∧ RHBatch01VerticalCenterValuesRight.values.length=55 := by decide +kernel
#print axioms solution
