-- Prove2me | solution 2 for TarchaBraids.thm_3_15_artin_presentation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-20T14:12:40.745979+00:00
-- url     : https://prove2.me/submissions/55809408-998f-4ebd-bc82-dd1d2edae39f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Theorems.Thm_TarchaBraids_thm_3_11_half_twists_generate
import Theorems.Thm_TarchaBraids_thm_3_15_half_twists_satisfy_relations
import Theorems.Thm_TarchaBraids_thm_3_15_half_twist_hom_injective

open BraidsLinksMCG TarchaBraids

/--
Artin's presentation theorem for the geometric braid group, assembled from:
1. the half-twists satisfying the Artin relations;
2. the half-twists generating the geometric braid group; and
3. injectivity of the induced homomorphism.
-/
theorem solution (n : ℕ) :
    ∃ f : ArtinBraidGroup n ≃* GeomBraidGroup n,
      ∀ i : Fin (n - 1), f (sigma i) = halfTwistBraid n i := by
  obtain ⟨hcomm, hbraid⟩ := thm_3_15_half_twists_satisfy_relations n

  have hrel : ∀ r ∈ braidRels n,
      FreeGroup.lift (fun i : Fin (n - 1) => halfTwistBraid n i) r = 1 := by
    rintro r (⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩)
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [hcomm i j hij]
      group
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [hbraid i j hij]
      group

  obtain ⟨hφ, hgen⟩ : ∃ f : ArtinBraidGroup n →* GeomBraidGroup n,
      ∀ i : Fin (n - 1), f (sigma i) = halfTwistBraid n i :=
    ⟨PresentedGroup.toGroup hrel, fun _ => PresentedGroup.toGroup.of hrel⟩

  have hsurj : Function.Surjective hφ := by
    rw [← MonoidHom.range_eq_top]
    have h1 : (⊤ : Subgroup (ArtinBraidGroup n))
        = Subgroup.closure (Set.range (fun i : Fin (n - 1) => sigma i)) :=
      (PresentedGroup.closure_range_of (braidRels n)).symm
    have h2 : Set.image hφ (Set.range (fun i : Fin (n - 1) => sigma i))
        = Set.range (fun i : Fin (n - 1) => halfTwistBraid n i) := by
      rw [← Set.range_comp]
      congr 1
      funext i
      exact hgen i
    calc
      hφ.range = Subgroup.map hφ ⊤ := by
        rw [MonoidHom.range_eq_map]
      _ = Subgroup.map hφ
          (Subgroup.closure (Set.range (fun i : Fin (n - 1) => sigma i))) := by
        rw [← h1]
      _ = Subgroup.closure
          (Set.image hφ (Set.range (fun i : Fin (n - 1) => sigma i))) :=
        MonoidHom.map_closure hφ _
      _ = Subgroup.closure
          (Set.range (fun i : Fin (n - 1) => halfTwistBraid n i)) := by
        rw [h2]
      _ = ⊤ := thm_3_11_half_twists_generate n

  have hinj : Function.Injective hφ :=
    thm_3_15_half_twist_hom_injective n hφ hgen

  exact ⟨MulEquiv.ofBijective hφ ⟨hinj, hsurj⟩, hgen⟩
