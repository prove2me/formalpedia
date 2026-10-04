-- Prove2me | solution 1 for TarchaBraids.geom_null_word_free_cancel_v1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T10:34:36.062188+00:00
-- url     : https://prove2.me/submissions/4345d64e-e170-4d23-87b2-7a7c61a381b6

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

open TarchaBraids in
theorem solution (n : ℕ) (u v : FreeGroup (Fin (n - 1)))
    (i : Fin (n - 1)) :
    FreeGroup.lift (halfTwistBraid n) (u * FreeGroup.of i * (FreeGroup.of i)⁻¹ * v) =
      FreeGroup.lift (halfTwistBraid n) (u * v) := by
  rw [mul_inv_cancel_right]
