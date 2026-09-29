-- Prove2me | solution 1 for TarchaBraids.halfTwist_hom_surjective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T18:13:40.762567+00:00
-- url     : https://prove2.me/submissions/b67b85da-aa5b-48b0-ac4f-12f41c401ef4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Theorems.Thm_TarchaBraids_halfTwist_free_lift_surjective_v1

open BraidsLinksMCG TarchaBraids

theorem solution (n : ℕ)
    (f : ArtinBraidGroup n →* GeomBraidGroup n)
    (hf : ∀ i : Fin (n - 1), f (sigma i) = halfTwistBraid n i) :
    Function.Surjective f := by
  intro y
  obtain ⟨w, hw⟩ :=
    TarchaBraids.halfTwist_free_lift_surjective_v1 n y
  refine ⟨PresentedGroup.mk (braidRels n) w, ?_⟩
  calc
    f (PresentedGroup.mk (braidRels n) w) =
        FreeGroup.lift (fun i : Fin (n - 1) => halfTwistBraid n i) w := by
      exact FreeGroup.lift_unique
        (f.comp (PresentedGroup.mk (braidRels n)))
        (fun i => by
          change f (sigma i) = halfTwistBraid n i
          exact hf i)
    _ = y := hw
