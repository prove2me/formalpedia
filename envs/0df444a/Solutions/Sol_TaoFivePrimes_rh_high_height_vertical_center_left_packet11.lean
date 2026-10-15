-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_left_packet11
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T08:55:39.303713+00:00
-- url     : https://prove2.me/submissions/b8f68d3b-b4df-4ff4-8449-a22c69aeedb0

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterLeft
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 RHHighVerticalCenter.packet ⟨0,by decide⟩ 11=((RHHighVerticalCenterLeft.rows[11]?).getD []) := by decide +kernel
