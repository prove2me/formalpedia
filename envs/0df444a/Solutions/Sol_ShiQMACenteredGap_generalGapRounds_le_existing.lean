-- Prove2me | solution 1 for ShiQMACenteredGap.generalGapRounds_le_existing
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-02T01:13:26.815712+00:00
-- url     : https://prove2.me/submissions/5fbc4692-789b-417d-802f-364f5f1c1217

import Definitions.Def_ShiQMACenteredGapDominatingSchedule
import Theorems.Thm_ShiQMACenteredGap_affine_schedule_le_rounds
import Theorems.Thm_ShiQMACenteredGap_generalGapRounds_controller_form

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAConstructiveSchedule

theorem solution (q p : Polynomial ℕ) (n : Nat) :
    generalGapRounds q p n ≤ rounds (gapPolynomial q p) n := by
  rw [generalGapRounds_controller_form]
  exact affine_schedule_le_rounds _ _ _
