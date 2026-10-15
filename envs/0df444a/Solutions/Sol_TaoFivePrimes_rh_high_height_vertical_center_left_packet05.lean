-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_left_packet05
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T08:16:23.870375+00:00
-- url     : https://prove2.me/submissions/88dfe36a-39bc-4a67-9f73-26b9e9fa9fb3

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterLeft
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 RHHighVerticalCenter.packet ⟨0,by decide⟩ 5=((RHHighVerticalCenterLeft.rows[5]?).getD []) := by decide +kernel
