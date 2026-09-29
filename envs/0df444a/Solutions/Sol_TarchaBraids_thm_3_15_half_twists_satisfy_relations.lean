-- Prove2me | solution 1 for TarchaBraids.thm_3_15_half_twists_satisfy_relations
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T03:06:16.637631+00:00
-- url     : https://prove2.me/submissions/1f3eb633-4414-48d4-9c7e-1fbf837425f0

import Theorems.Thm_TarchaBraids_thm_3_15_half_twists_commute
import Theorems.Thm_TarchaBraids_thm_3_15_half_twists_braid_relation
import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option linter.all false

open BraidsLinksMCG TarchaBraids

theorem _root_.solution (n : ℕ) :
    (∀ i j : Fin (n - 1), 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs →
        halfTwistBraid n i * halfTwistBraid n j = halfTwistBraid n j * halfTwistBraid n i) ∧
    (∀ i j : Fin (n - 1), (j : ℕ) = (i : ℕ) + 1 →
      halfTwistBraid n i * halfTwistBraid n j * halfTwistBraid n i =
        halfTwistBraid n j * halfTwistBraid n i * halfTwistBraid n j) :=
  ⟨TarchaBraids.thm_3_15_half_twists_commute n,
   TarchaBraids.thm_3_15_half_twists_braid_relation n⟩

#print axioms solution
