-- Prove2me | solution 1 for TarchaBraids.thm_3_15_half_twists_commute
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T07:56:12.587427+00:00
-- url     : https://prove2.me/submissions/cb4b4df1-5962-4bbc-8543-8ac8264d15dc

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Theorems.Thm_TarchaBraids_thm_3_15_half_twists_far_commute_v1

open TarchaBraids

theorem solution (n : ℕ) :
    ∀ i j : Fin (n - 1), 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs →
      halfTwistBraid n i * halfTwistBraid n j = halfTwistBraid n j * halfTwistBraid n i :=
  TarchaBraids.thm_3_15_half_twists_far_commute_v1 n
