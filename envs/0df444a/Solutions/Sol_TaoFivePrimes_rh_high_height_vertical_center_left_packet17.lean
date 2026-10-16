-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_vertical_center_left_packet17
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T10:53:08.409565+00:00
-- url     : https://prove2.me/submissions/e86db576-696b-42e3-9822-a3f58c568de6

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighVerticalCenterLeft
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 RHHighVerticalCenter.packet ⟨0,by decide⟩ 17=((RHHighVerticalCenterLeft.rows[17]?).getD []) := by decide +kernel
