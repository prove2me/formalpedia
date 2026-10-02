-- Prove2me | solution 1 for ShiQMACenteredGap.biasIter_mono
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-01T23:54:22.758425+00:00
-- url     : https://prove2.me/submissions/d58f3106-3c87-46c2-b00a-3d8e3d941c2a

import Definitions.Def_ShiQMACenteredGapGeneralSchedule
import Theorems.Thm_ShiQMACenteredGap_biasStep_mono
import Theorems.Thm_ShiQMACenteredGap_biasIter_bounds

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAErrorIteration ShiQMAConstructiveSchedule

theorem solution {d e : ℝ} (hd : 0 ≤ d) (hde : d ≤ e)
    (he : e ≤ 1 / 2) (r : Nat) : biasIter d r ≤ biasIter e r := by
  induction r with
  | zero => exact hde
  | succ r ih =>
    exact biasStep_mono (biasIter_bounds hd (hde.trans he) r).1 ih
      (biasIter_bounds (hd.trans hde) he r).2
