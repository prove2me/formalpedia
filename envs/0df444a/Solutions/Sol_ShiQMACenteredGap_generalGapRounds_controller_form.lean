-- Prove2me | solution 1 for ShiQMACenteredGap.generalGapRounds_controller_form
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-02T00:33:36.064062+00:00
-- url     : https://prove2.me/submissions/f9287952-0598-4d46-ae84-639f8e788663

import Definitions.Def_ShiQMACenteredGapGeneralSchedule

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAErrorIteration ShiQMAConstructiveSchedule

theorem solution (q p : Polynomial ℕ) (n : Nat) :
    generalGapRounds q p n =
      (3 * (Nat.log 2 (q.eval 1 + 1) + 4) + Nat.log 2 (p.eval 1 + 1) + 4) +
      (3 * q.natDegree + p.natDegree) * (Nat.log 2 (n + 1) + 1) := by
  dsimp [generalGapRounds, normalizationRounds, rounds, exponentBudget]
  ring
