-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_left_packet03
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T08:07:18.920577+00:00
-- url     : https://prove2.me/submissions/580ef164-8420-4757-875e-a720e4513f03

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterLeft
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 RHHighVerticalCenter.packet ⟨0,by decide⟩ 3=((RHHighVerticalCenterLeft.rows[3]?).getD []) := by decide +kernel
