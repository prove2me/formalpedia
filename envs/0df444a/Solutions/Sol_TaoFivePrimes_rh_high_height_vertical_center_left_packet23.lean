-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_left_packet23
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T12:20:49.436167+00:00
-- url     : https://prove2.me/submissions/011c5e12-a1f0-4b93-8bea-cc0d23a45c7c

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterLeft
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 RHHighVerticalCenter.packet ⟨0,by decide⟩ 23=((RHHighVerticalCenterLeft.rows[23]?).getD []) := by decide +kernel
