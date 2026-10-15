-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_left_packet12
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T09:04:17.206743+00:00
-- url     : https://prove2.me/submissions/6d38a0f4-04ae-4b21-84b4-013fa0ad60da

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterLeft
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 RHHighVerticalCenter.packet ⟨0,by decide⟩ 12=((RHHighVerticalCenterLeft.rows[12]?).getD []) := by decide +kernel
