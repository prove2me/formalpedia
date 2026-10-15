-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_left_packet09
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T08:38:10.378012+00:00
-- url     : https://prove2.me/submissions/c38a01d4-6d10-41b7-9cf1-67057c81a746

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterLeft
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 RHHighVerticalCenter.packet ⟨0,by decide⟩ 9=((RHHighVerticalCenterLeft.rows[9]?).getD []) := by decide +kernel
