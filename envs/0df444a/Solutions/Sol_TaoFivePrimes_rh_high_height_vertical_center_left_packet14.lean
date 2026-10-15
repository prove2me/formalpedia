-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_left_packet14
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T09:44:03.37512+00:00
-- url     : https://prove2.me/submissions/7d42328e-eb83-47de-a236-8c1048a8cb9c

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterLeft
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 RHHighVerticalCenter.packet ⟨0,by decide⟩ 14=((RHHighVerticalCenterLeft.rows[14]?).getD []) := by decide +kernel
