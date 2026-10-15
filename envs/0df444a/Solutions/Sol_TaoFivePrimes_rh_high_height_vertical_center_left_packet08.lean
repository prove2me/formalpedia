-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_left_packet08
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T08:36:31.921099+00:00
-- url     : https://prove2.me/submissions/f1b8d009-e934-45b3-81f4-eaf6cb0801c0

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterLeft
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 RHHighVerticalCenter.packet ⟨0,by decide⟩ 8=((RHHighVerticalCenterLeft.rows[8]?).getD []) := by decide +kernel
