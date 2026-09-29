-- Prove2me | solution 1 for SocialEquilibrium.Existence.isPolyhedron_prod
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:22:55.192811+00:00
-- url     : https://prove2.me/submissions/00af4f54-b7ee-4305-8fb2-eeff14ba8baa

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_IsPolyhedron

namespace SocialEquilibrium.Existence

theorem aux_ipp_cell_prod {A B : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] {C : Set A} {D : Set B}
    (hC : IsConvexCell C) (hD : IsConvexCell D) : IsConvexCell (C ×ˢ D) := by
  obtain ⟨s, hs, rfl⟩ := hC
  obtain ⟨t, ht, rfl⟩ := hD
  refine ⟨s ×ˢ t, hs.product ht, ?_⟩
  rw [Finset.coe_product, convexHull_prod]

theorem aux_ipp_geom_prod {A B : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] {P : Set A} {Q : Set B}
    (hP : IsGeometricPolyhedron P) (hQ : IsGeometricPolyhedron Q) :
    IsGeometricPolyhedron (P ×ˢ Q) := by
  classical
  obtain ⟨S, hS, rfl⟩ := hP
  obtain ⟨T, hT, rfl⟩ := hQ
  refine ⟨(S ×ˢ T).image (fun p => p.1 ×ˢ p.2), ?_, ?_⟩
  · intro X hX
    simp only [Finset.mem_image, Finset.mem_product] at hX
    obtain ⟨⟨C, D⟩, ⟨hC, hD⟩, rfl⟩ := hX
    exact aux_ipp_cell_prod (hS C hC) (hT D hD)
  · ext ⟨x, y⟩
    simp only [Set.mem_prod, Set.mem_iUnion, Finset.mem_image, Finset.mem_product,
      exists_prop, Prod.exists]
    constructor
    · rintro ⟨⟨C, hC, hx⟩, ⟨D, hD, hy⟩⟩
      exact ⟨C ×ˢ D, ⟨C, D, ⟨hC, hD⟩, rfl⟩, hx, hy⟩
    · rintro ⟨X, ⟨C, D, ⟨hC, hD⟩, rfl⟩, hx, hy⟩
      exact ⟨⟨C, hC, hx⟩, ⟨D, hD, hy⟩⟩

theorem aux_ipp_geom_image {A B : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] (f : A →ₗ[ℝ] B) {P : Set A}
    (hP : IsGeometricPolyhedron P) : IsGeometricPolyhedron (f '' P) := by
  classical
  obtain ⟨S, hS, rfl⟩ := hP
  refine ⟨S.image (fun C => f '' C), ?_, ?_⟩
  · intro X hX
    simp only [Finset.mem_image] at hX
    obtain ⟨C, hC, rfl⟩ := hX
    obtain ⟨s, hs, rfl⟩ := hS C hC
    refine ⟨s.image f, hs.image f, ?_⟩
    rw [Finset.coe_image, LinearMap.image_convexHull]
  · rw [Set.image_iUnion₂]
    ext z
    simp only [Set.mem_iUnion, Finset.mem_image, exists_prop]
    constructor
    · rintro ⟨C, hC, hz⟩
      exact ⟨f '' C, ⟨C, hC, rfl⟩, hz⟩
    · rintro ⟨X, ⟨C, hC, rfl⟩, hz⟩
      exact ⟨C, hC, hz⟩

end SocialEquilibrium.Existence

open SocialEquilibrium.Existence

theorem solution {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {P : Set E} {Q : Set F} (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) :
    IsPolyhedron (P ×ˢ Q) := by
  obtain ⟨m, P', hP', ⟨eP⟩⟩ := hP
  obtain ⟨n, Q', hQ', ⟨eQ⟩⟩ := hQ
  have hrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + n))) := by
    simp [Module.finrank_prod]
  let L : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (m + n)) := ContinuousLinearEquiv.ofFinrankEq hrank
  refine ⟨m + n, L '' (P' ×ˢ Q'), ?_, ?_⟩
  · exact aux_ipp_geom_image L.toLinearEquiv.toLinearMap (aux_ipp_geom_prod hP' hQ')
  exact ⟨((Homeomorph.Set.prod P Q).trans (eP.prodCongr eQ)).trans
    ((Homeomorph.Set.prod P' Q').symm.trans (L.toHomeomorph.image (P' ×ˢ Q')))⟩
