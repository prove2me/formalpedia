-- Prove2me | solution 1 for TarchaBraids.halfTwist_free_lift_surjective_v1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T19:43:47.765829+00:00
-- url     : https://prove2.me/submissions/1e2b28c8-15d1-4133-92bd-d34941ea2bce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TarchaBraids_thm_3_11_half_twists_generate
import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG TarchaBraids

theorem _root_.solution (n : ℕ) :
    Function.Surjective
      (FreeGroup.lift (fun i : Fin (n - 1) => halfTwistBraid n i)) := by
  rw [← MonoidHom.range_eq_top, MonoidHom.range_eq_map,
    ← FreeGroup.closure_range_of (Fin (n - 1)), MonoidHom.map_closure,
    ← Set.range_comp]
  have hcomp : (⇑(FreeGroup.lift (fun i : Fin (n - 1) => halfTwistBraid n i)) ∘ FreeGroup.of)
      = fun i : Fin (n - 1) => halfTwistBraid n i := by
    funext i
    exact FreeGroup.lift_apply_of
  rw [hcomp]
  exact TarchaBraids.thm_3_11_half_twists_generate n

#print axioms solution
