-- Prove2me | solution 3 for TarchaBraids.thm_3_15_artin_presentation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T17:29:01.553293+00:00
-- url     : https://prove2.me/submissions/424aceb3-e907-48b9-b1ae-4e42733f0b0b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TarchaBraids_thm_3_15_half_twists_satisfy_relations
import Theorems.Thm_TarchaBraids_halfTwist_hom_surjective
import Theorems.Thm_TarchaBraids_thm_3_15_half_twist_hom_injective
import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG TarchaBraids

theorem _root_.solution (n : ℕ) :
    ∃ f : ArtinBraidGroup n ≃* GeomBraidGroup n,
      ∀ i : Fin (n - 1), f (sigma i) = halfTwistBraid n i := by
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
  have hf : ∀ i : Fin (n - 1),
      PresentedGroup.toGroup hrel (sigma i) = halfTwistBraid n i :=
    fun i => PresentedGroup.toGroup.of hrel
  have hs := TarchaBraids.halfTwist_hom_surjective n (PresentedGroup.toGroup hrel) hf
  have hi := TarchaBraids.thm_3_15_half_twist_hom_injective n (PresentedGroup.toGroup hrel) hf
  exact ⟨MulEquiv.ofBijective _ ⟨hi, hs⟩, hf⟩

#print axioms solution
