-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_left_packet19
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T11:02:32.759636+00:00
-- url     : https://prove2.me/submissions/6e1bfcc7-de14-4fc9-9df8-07cea57aeba5

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterLeft
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 RHHighVerticalCenter.packet ⟨0,by decide⟩ 19=((RHHighVerticalCenterLeft.rows[19]?).getD []) := by decide +kernel
