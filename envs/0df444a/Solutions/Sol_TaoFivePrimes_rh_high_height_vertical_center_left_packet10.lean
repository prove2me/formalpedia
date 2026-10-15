-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_left_packet10
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T08:51:48.170775+00:00
-- url     : https://prove2.me/submissions/76912469-744e-4af7-a9fc-5422aabe2f0c

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterLeft
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 RHHighVerticalCenter.packet ⟨0,by decide⟩ 10=((RHHighVerticalCenterLeft.rows[10]?).getD []) := by decide +kernel
