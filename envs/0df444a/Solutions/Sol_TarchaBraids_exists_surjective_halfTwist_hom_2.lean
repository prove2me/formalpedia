-- Prove2me | solution 2 for TarchaBraids.exists_surjective_halfTwist_hom
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T18:06:04.30257+00:00
-- url     : https://prove2.me/submissions/46fc4310-c93b-4031-aee6-89eca9e22170
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Theorems.Thm_TarchaBraids_exists_halfTwist_hom_v1
import Theorems.Thm_TarchaBraids_halfTwist_hom_surjective

open BraidsLinksMCG TarchaBraids

theorem solution (n : ℕ) :
    ∃ f : ArtinBraidGroup n →* GeomBraidGroup n,
      (∀ i : Fin (n - 1), f (sigma i) = halfTwistBraid n i) ∧
        Function.Surjective f := by
  obtain ⟨f, hf⟩ := TarchaBraids.exists_halfTwist_hom_v1 n
  exact ⟨f, hf, TarchaBraids.halfTwist_hom_surjective n f hf⟩
