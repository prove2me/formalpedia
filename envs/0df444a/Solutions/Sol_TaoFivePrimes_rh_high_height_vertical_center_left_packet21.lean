-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_left_packet21
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T11:35:49.919337+00:00
-- url     : https://prove2.me/submissions/262d6c4c-e253-438e-8f06-ec6dfc5028cf

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterLeft
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 RHHighVerticalCenter.packet ⟨0,by decide⟩ 21=((RHHighVerticalCenterLeft.rows[21]?).getD []) := by decide +kernel
