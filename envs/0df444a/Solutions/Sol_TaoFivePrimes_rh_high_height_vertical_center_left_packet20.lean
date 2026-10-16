-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_left_packet20
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T11:06:44.271051+00:00
-- url     : https://prove2.me/submissions/b7498c66-28e8-4c87-a8d1-1acc32f22747

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterLeft
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 RHHighVerticalCenter.packet ⟨0,by decide⟩ 20=((RHHighVerticalCenterLeft.rows[20]?).getD []) := by decide +kernel
