-- Prove2me | solution 1 for ShiQMACenteredGap.biasIter_add
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-02T00:03:00.645455+00:00
-- url     : https://prove2.me/submissions/1851759c-171c-45ac-ba73-ce0633b67c18

import Definitions.Def_ShiQMACenteredGapGeneralSchedule

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAErrorIteration ShiQMAConstructiveSchedule

theorem solution (d : ℝ) (r s : Nat) :
    biasIter d (r + s) = biasIter (biasIter d r) s := by
  induction s with
  | zero => rfl
  | succ s ih => exact congrArg biasStep ih
