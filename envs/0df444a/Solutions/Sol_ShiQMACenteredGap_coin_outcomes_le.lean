-- Prove2me | solution 1 for ShiQMACenteredGap.coin_outcomes_le
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-01T09:54:50.702914+00:00
-- url     : https://prove2.me/submissions/d954461c-3d36-4ad7-a974-63d0f4aa8568

import Definitions.Def_ShiQMACenteredGapScalarCentering
import Mathlib.Tactic
import Mathlib.Data.Real.Archimedean

set_option autoImplicit false

open ShiQMACenteredGap

theorem solution (q : Nat) (hq : 0 < q) :
    2 ^ coinBits q ≤ 8 * q := by
  have hlog := Nat.pow_log_le_self 2 (show 4 * q ≠ 0 by omega)
  dsimp [coinBits]
  rw [pow_succ]
  omega
