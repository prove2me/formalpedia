-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_left_packet13
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T09:34:03.885052+00:00
-- url     : https://prove2.me/submissions/50efc5ac-9634-4e80-b6bd-7c55a625b912

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterLeft
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 RHHighVerticalCenter.packet ⟨0,by decide⟩ 13=((RHHighVerticalCenterLeft.rows[13]?).getD []) := by decide +kernel
