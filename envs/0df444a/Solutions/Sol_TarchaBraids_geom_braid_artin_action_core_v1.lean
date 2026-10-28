-- Prove2me | solution 1 for TarchaBraids.geom_braid_artin_action_core_v1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:26:41.003982+00:00
-- url     : https://prove2.me/submissions/625a1f6a-eb8c-4ed2-9d71-1d8521696c4d

import Theorems.Thm_TarchaBraids_geom_braid_artin_action

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinEndo
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

open TarchaBraids

open BraidsLinksMCG

theorem solution (n : ℕ) :
    ∃ rho : GeomBraidGroup n →* MulAut (FreeGroup (Fin n)),
      ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n),
        rho (halfTwistBraid n i) w = artinEndo n i w := by
  apply TarchaBraids.geom_braid_artin_action <;> assumption


