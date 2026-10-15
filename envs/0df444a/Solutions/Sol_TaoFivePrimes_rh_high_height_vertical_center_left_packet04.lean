-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_left_packet04
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T08:04:59.841896+00:00
-- url     : https://prove2.me/submissions/630397ae-6b5a-42ac-b8a2-3586f91c8aa7

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterLeft
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 RHHighVerticalCenter.packet ⟨0,by decide⟩ 4=((RHHighVerticalCenterLeft.rows[4]?).getD []) := by decide +kernel
