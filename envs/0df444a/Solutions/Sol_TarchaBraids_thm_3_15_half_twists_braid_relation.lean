-- Prove2me | solution 1 for TarchaBraids.thm_3_15_half_twists_braid_relation
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T17:27:31.929272+00:00
-- url     : https://prove2.me/submissions/74493a31-1c1f-42a2-a7e8-e30a04ebcba6

import Theorems.Thm_TarchaBraids_thm_3_15_half_twists_adjacent_braid_v1
import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG TarchaBraids

theorem _root_.solution (n : ℕ) :
    ∀ i j : Fin (n - 1), (j : ℕ) = (i : ℕ) + 1 →
      halfTwistBraid n i * halfTwistBraid n j * halfTwistBraid n i =
        halfTwistBraid n j * halfTwistBraid n i * halfTwistBraid n j :=
  TarchaBraids.thm_3_15_half_twists_adjacent_braid_v1 n

#print axioms solution
