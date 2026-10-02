-- Prove2me | solution 1 for ShiQMACenteredGap.copies_generalGapRounds_le
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-02T00:41:09.822327+00:00
-- url     : https://prove2.me/submissions/660c1d25-cddb-4243-a523-835e34c9c99a

import Definitions.Def_ShiQMACenteredGapGeneralSchedule
import Theorems.Thm_ShiQMAConstructiveSchedule_copies_rounds_le

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAErrorIteration ShiQMAConstructiveSchedule

theorem solution (q p : Polynomial ℕ) (n : Nat) :
    3 ^ generalGapRounds q p n ≤
      (3 ^ (Nat.log 2 (q.eval 1 + 1) + q.natDegree + 4) *
        (n + 1) ^ (2 * q.natDegree)) ^ 3 *
      (3 ^ (Nat.log 2 (p.eval 1 + 1) + p.natDegree + 4) *
        (n + 1) ^ (2 * p.natDegree)) := by
  have hq := Nat.pow_le_pow_left (copies_rounds_le q n) 3
  have hp := copies_rounds_le p n
  dsimp [generalGapRounds, normalizationRounds]
  rw [pow_add, Nat.mul_comm 3 (rounds q n), pow_mul]
  exact Nat.mul_le_mul hq hp
