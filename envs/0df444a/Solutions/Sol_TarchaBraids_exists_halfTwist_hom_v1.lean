-- Prove2me | solution 1 for TarchaBraids.exists_halfTwist_hom_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T18:00:28.672416+00:00
-- url     : https://prove2.me/submissions/4d43ff82-9389-4bfe-b5a6-6947c86526e7

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Theorems.Thm_TarchaBraids_thm_3_15_half_twists_satisfy_relations

open BraidsLinksMCG TarchaBraids

theorem solution (n : ℕ) :
    ∃ f : ArtinBraidGroup n →* GeomBraidGroup n,
      ∀ i : Fin (n - 1), f (sigma i) = halfTwistBraid n i := by
  obtain ⟨hcomm, hbraid⟩ :=
    TarchaBraids.thm_3_15_half_twists_satisfy_relations n
  have hrel : ∀ r ∈ braidRels n,
      FreeGroup.lift (fun i : Fin (n - 1) => halfTwistBraid n i) r = 1 := by
    rintro r (⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩)
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [hcomm i j hij]
      group
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [hbraid i j hij]
      group
  exact ⟨PresentedGroup.toGroup hrel, fun _ => PresentedGroup.toGroup.of hrel⟩
