-- Prove2me | solution 1 for TarchaBraids.geom_braid_relator_word_null_v1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-04T16:04:33.573074+00:00
-- url     : https://prove2.me/submissions/71d52faf-2012-486b-885c-999c1a03f75a

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Theorems.Thm_TarchaBraids_thm_3_15_half_twists_satisfy_relations

set_option autoImplicit false

namespace TarchaBraids

theorem geom_braid_relator_word_null_v1 (n : ℕ) (r : FreeGroup (Fin (n - 1)))
    (hr : r ∈ BraidsLinksMCG.braidRels n) :
    FreeGroup.lift (halfTwistBraid n) r = 1 := by
  rcases hr with ⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [(thm_3_15_half_twists_satisfy_relations n).1 i j hij]
    group
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [(thm_3_15_half_twists_satisfy_relations n).2 i j hij]
    exact mul_inv_cancel _

end TarchaBraids

theorem solution (n : ℕ) (r : FreeGroup (Fin (n - 1)))
    (hr : r ∈ BraidsLinksMCG.braidRels n) :
    FreeGroup.lift (TarchaBraids.halfTwistBraid n) r = 1 :=
  TarchaBraids.geom_braid_relator_word_null_v1 n r hr
