-- Prove2me | solution 1 for TarchaBraids.thm_3_15_artin_presentation
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T05:36:02.073978+00:00
-- url     : https://prove2.me/submissions/1c92bf2c-90f6-428f-97cb-95c89f2e7a86

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Theorems.Thm_TarchaBraids_thm_3_11_half_twists_generate
import Theorems.Thm_TarchaBraids_thm_3_15_half_twists_satisfy_relations
import Theorems.Thm_TarchaBraids_thm_3_15_half_twist_hom_injective

open BraidsLinksMCG TarchaBraids

theorem solution (n : ℕ) :
    ∃ f : ArtinBraidGroup n ≃* GeomBraidGroup n,
      ∀ i : Fin (n - 1), f (sigma i) = halfTwistBraid n i := by
  obtain ⟨hcomm, hbraid⟩ := thm_3_15_half_twists_satisfy_relations n
  -- the half-twists satisfy the defining relators, so the generator map extends to `B_n`
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
  -- surjectivity, from the fact that the half-twists generate
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
    calc hφ.range = Subgroup.map hφ ⊤ := by
          rw [MonoidHom.range_eq_map]
      _ = Subgroup.map hφ (Subgroup.closure (Set.range (fun i : Fin (n - 1) => sigma i))) := by
          rw [← h1]
      _ = Subgroup.closure (Set.image hφ (Set.range (fun i : Fin (n - 1) => sigma i))) :=
          MonoidHom.map_closure hφ _
      _ = Subgroup.closure (Set.range (fun i : Fin (n - 1) => halfTwistBraid n i)) := by rw [h2]
      _ = ⊤ := thm_3_11_half_twists_generate n
  -- injectivity
  have hinj : Function.Injective hφ := thm_3_15_half_twist_hom_injective n hφ hgen
  exact ⟨MulEquiv.ofBijective hφ ⟨hinj, hsurj⟩, hgen⟩
