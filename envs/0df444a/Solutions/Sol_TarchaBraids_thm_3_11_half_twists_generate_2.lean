-- Prove2me | solution 2 for TarchaBraids.thm_3_11_half_twists_generate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T17:30:59.595072+00:00
-- url     : https://prove2.me/submissions/c5d5d0d2-df7f-4913-9cec-54ced31f8945
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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
    Subgroup.closure (Set.range (fun i : Fin (n - 1) => halfTwistBraid n i)) =
      (⊤ : Subgroup (GeomBraidGroup n)) := by
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
  have hrange : Set.range (fun i : Fin (n - 1) => halfTwistBraid n i) =
      (PresentedGroup.toGroup hrel) '' (Set.range (fun i : Fin (n - 1) => sigma i)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨sigma i, ⟨i, rfl⟩, hf i⟩
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hf i).symm⟩
  have hsig : Set.range (fun i : Fin (n - 1) => sigma i) =
      Set.range (PresentedGroup.of (rels := braidRels n)) := rfl
  calc Subgroup.closure (Set.range (fun i : Fin (n - 1) => halfTwistBraid n i))
      = Subgroup.closure
          ((PresentedGroup.toGroup hrel) '' (Set.range (fun i : Fin (n - 1) => sigma i))) :=
        congrArg Subgroup.closure hrange
    _ = Subgroup.map (PresentedGroup.toGroup hrel)
          (Subgroup.closure (Set.range (fun i : Fin (n - 1) => sigma i))) :=
        (MonoidHom.map_closure _ _).symm
    _ = Subgroup.map (PresentedGroup.toGroup hrel) (⊤ : Subgroup (ArtinBraidGroup n)) :=
        congrArg (Subgroup.map (PresentedGroup.toGroup hrel))
          ((congrArg Subgroup.closure hsig).trans
            (PresentedGroup.closure_range_of (braidRels n)))
    _ = (⊤ : Subgroup (GeomBraidGroup n)) := Subgroup.map_top_of_surjective _ hs

#print axioms solution
