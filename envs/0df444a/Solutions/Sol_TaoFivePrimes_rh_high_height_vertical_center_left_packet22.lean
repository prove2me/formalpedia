-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_left_packet22
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T12:03:52.108172+00:00
-- url     : https://prove2.me/submissions/7b98a14f-ffe8-4284-bab8-5e9ff46cd3e8

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterLeft
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 RHHighVerticalCenter.packet ⟨0,by decide⟩ 22=((RHHighVerticalCenterLeft.rows[22]?).getD []) := by decide +kernel
