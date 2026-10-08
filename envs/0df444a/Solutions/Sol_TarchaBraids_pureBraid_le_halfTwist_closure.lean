-- Prove2me | solution 1 for TarchaBraids.pureBraid_le_halfTwist_closure
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T20:46:34.429312+00:00
-- url     : https://prove2.me/submissions/ef6cbcb4-e5a2-46ea-9a48-9a163d392897

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Theorems.Thm_TarchaBraids_thm_3_11_half_twists_generate

/-!
# The pure braid image lies in the half-twist closure

Once `thm_3_11_half_twists_generate` is available the half-twist closure is the whole group,
so *every* subgroup — in particular the image of the pure braid group under `configProj` —
is contained in it.  The point of recording this is structural: this leaf carries no content
beyond `thm_3_11`.
-/

open TarchaBraids BraidsLinksMCG

theorem solution (n : ℕ) :
    (FundamentalGroup.map (configProj n) (baseOrdered n)).range ≤
      Subgroup.closure (Set.range (fun i : Fin (n - 1) => halfTwistBraid n i)) := by
  rw [TarchaBraids.thm_3_11_half_twists_generate n]
  exact le_top
