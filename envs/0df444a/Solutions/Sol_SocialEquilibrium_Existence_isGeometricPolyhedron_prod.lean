-- Prove2me | solution 1 for SocialEquilibrium.Existence.isGeometricPolyhedron_prod
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:23:58.447663+00:00
-- url     : https://prove2.me/submissions/82e3bd4e-b557-4355-af1b-2bb79e77b70c

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_IsPolyhedron

namespace SocialEquilibrium.Existence

theorem aux_gpp_cell_prod {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    {C : Set E} {D : Set F} (hC : IsConvexCell C) (hD : IsConvexCell D) :
    IsConvexCell (C ×ˢ D) := by
  obtain ⟨s, hs, rfl⟩ := hC
  obtain ⟨t, ht, rfl⟩ := hD
  refine ⟨s ×ˢ t, hs.product ht, ?_⟩
  rw [Finset.coe_product, convexHull_prod]

end SocialEquilibrium.Existence

open SocialEquilibrium.Existence

theorem solution {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {P : Set E} {Q : Set F} (hP : IsGeometricPolyhedron P) (hQ : IsGeometricPolyhedron Q) :
    IsGeometricPolyhedron (P ×ˢ Q) := by
  classical
  obtain ⟨S, hS, rfl⟩ := hP
  obtain ⟨T, hT, rfl⟩ := hQ
  refine ⟨(S ×ˢ T).image (fun p => p.1 ×ˢ p.2), ?_, ?_⟩
  · intro C hC
    obtain ⟨⟨A, B⟩, hAB, rfl⟩ := Finset.mem_image.mp hC
    rw [Finset.mem_product] at hAB
    exact aux_gpp_cell_prod (hS A hAB.1) (hT B hAB.2)
  · ext ⟨x, y⟩
    simp only [Set.mem_prod, Set.mem_iUnion, Finset.mem_image, Finset.mem_product,
      Prod.exists, exists_prop]
    constructor
    · rintro ⟨⟨A, hA, hxA⟩, ⟨B, hB, hyB⟩⟩
      exact ⟨A ×ˢ B, ⟨A, B, ⟨hA, hB⟩, rfl⟩, hxA, hyB⟩
    · rintro ⟨C, ⟨A, B, ⟨hA, hB⟩, rfl⟩, hxA, hyB⟩
      exact ⟨⟨A, hA, hxA⟩, ⟨B, hB, hyB⟩⟩
