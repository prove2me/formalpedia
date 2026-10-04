-- Prove2me | solution 2 for TarchaBraids.geom_null_word_conj_insert_v1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-03T10:45:17.313379+00:00
-- url     : https://prove2.me/submissions/0e357f3e-7617-40a4-b372-72f2220dedb9

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

open TarchaBraids

theorem solution (n : ℕ) (u r : FreeGroup (Fin (n - 1)))
    (hr : FreeGroup.lift (halfTwistBraid n) r = 1) :
    FreeGroup.lift (halfTwistBraid n) (u * r * u⁻¹) = 1 := by
  have hmap :
      FreeGroup.lift (halfTwistBraid n) (u * r * u⁻¹) =
        FreeGroup.lift (halfTwistBraid n) u *
          FreeGroup.lift (halfTwistBraid n) r *
          (FreeGroup.lift (halfTwistBraid n) u)⁻¹ := by
    simp [map_mul, map_inv]
  rw [hmap, hr, mul_one, mul_inv_cancel]
