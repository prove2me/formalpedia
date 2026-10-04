-- Prove2me | solution 1 for TarchaBraids.geom_null_word_conj_insert_v1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T10:35:23.207987+00:00
-- url     : https://prove2.me/submissions/90694297-263d-4d47-89d1-e31bdd96c9a0

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

open TarchaBraids in
theorem solution (n : ℕ) (u r : FreeGroup (Fin (n - 1)))
    (hr : FreeGroup.lift (halfTwistBraid n) r = 1) :
    FreeGroup.lift (halfTwistBraid n) (u * r * u⁻¹) = 1 := by
  rw [map_mul, map_mul, hr, mul_one, map_inv, mul_inv_cancel]
