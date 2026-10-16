-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_left_packet18
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T10:55:56.439314+00:00
-- url     : https://prove2.me/submissions/4c65d91a-35ae-4a5a-9c49-e48083d270c8

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterLeft
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 RHHighVerticalCenter.packet ⟨0,by decide⟩ 18=((RHHighVerticalCenterLeft.rows[18]?).getD []) := by decide +kernel
