-- Prove2me | solution 1 for TarchaBraids.exists_surjective_halfTwist_hom
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T17:05:00.027663+00:00
-- url     : https://prove2.me/submissions/46549045-7e57-4d0a-bc05-c4bcd23545d1

import Theorems.Thm_TarchaBraids_thm_3_15_half_twists_satisfy_relations
import Theorems.Thm_TarchaBraids_halfTwist_hom_surjective
import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG TarchaBraids

theorem _root_.solution (n : ℕ) :
    ∃ f : ArtinBraidGroup n →* GeomBraidGroup n,
      (∀ i : Fin (n - 1), f (sigma i) = halfTwistBraid n i) ∧
        Function.Surjective f := by
  obtain ⟨hcomm, hbraid⟩ := TarchaBraids.thm_3_15_half_twists_satisfy_relations n
  have hrel : ∀ r ∈ braidRels n,
      FreeGroup.lift (fun i : Fin (n - 1) => halfTwistBraid n i) r = 1 := by
    intro r hr
    rcases hr with ⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩
    · have h := hcomm i j hij
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [h]; group
    · have h := hbraid i j hij
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [h]; group
  refine ⟨PresentedGroup.toGroup hrel, fun i => PresentedGroup.toGroup.of hrel, ?_⟩
  exact TarchaBraids.halfTwist_hom_surjective n _ (fun i => PresentedGroup.toGroup.of hrel)

#print axioms solution
