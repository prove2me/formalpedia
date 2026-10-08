-- Prove2me | solution 1 for SocialEquilibrium.Existence.pi_isPolyhedron_isContractible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T07:52:07.474288+00:00
-- url     : https://prove2.me/submissions/8cdb0c17-d0bf-465d-823d-be5c7fcd4330

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_IsPolyhedron
import Definitions.Def_SocialEquilibrium_Existence_IsContractible

set_option autoImplicit false

universe u v

namespace F0701a6c

open SocialEquilibrium.Existence

theorem geom_image {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (f : E →ₗ[ℝ] F) {P : Set E} (h : IsGeometricPolyhedron P) :
    IsGeometricPolyhedron (f '' P) := by
  classical
  obtain ⟨S, hS, rfl⟩ := h
  refine ⟨S.image (fun C => f '' C), ?_, ?_⟩
  · intro C hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.1 hC
    obtain ⟨s, hs, rfl⟩ := hS D hD
    exact ⟨s.image f, hs.image f, by rw [Finset.coe_image, f.image_convexHull]⟩
  · ext x
    simp only [Set.image_iUnion₂, Set.mem_iUnion, Finset.mem_image, exists_prop]
    constructor
    · rintro ⟨C, hC, hx⟩
      exact ⟨f '' C, ⟨C, hC, rfl⟩, hx⟩
    · rintro ⟨_, ⟨C, hC, rfl⟩, hx⟩
      exact ⟨C, hC, hx⟩

theorem geom_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (Q : ∀ i, Set (E i)) (h : ∀ i, IsGeometricPolyhedron (Q i)) :
    IsGeometricPolyhedron (Set.univ.pi Q) := by
  classical
  choose S hS hQ using h
  refine ⟨(Finset.univ : Finset (∀ i, S i)).image
    (fun c => Set.univ.pi (fun i => ((c i : Set (E i))))), ?_, ?_⟩
  · intro C hC
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hC
    choose s hs hc using fun i => hS i (c i) (c i).2
    refine ⟨Fintype.piFinset s, Fintype.piFinset_nonempty.2 hs, ?_⟩
    rw [Fintype.coe_piFinset, convexHull_pi]
    congr 1
    funext i
    exact hc i
  · ext x
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_iUnion, Finset.mem_image,
      Finset.mem_univ, true_and, exists_prop]
    constructor
    · intro hx
      have hx' : ∀ i, ∃ C ∈ S i, x i ∈ C := by
        intro i
        have := hx i
        rw [hQ i] at this
        simpa using this
      choose C hC hxC using hx'
      exact ⟨_, ⟨fun i => ⟨C i, hC i⟩, rfl⟩, fun i _ => hxC i⟩
    · rintro ⟨_, ⟨c, rfl⟩, hx⟩ i
      rw [hQ i]
      exact Set.mem_biUnion (c i).2 (hx i (Set.mem_univ i))

def univPiHomeo {ι : Type*} {E : ι → Type*} [∀ i, TopologicalSpace (E i)]
    (X : ∀ i, Set (E i)) : (Set.univ.pi X) ≃ₜ (∀ i, X i) where
  toEquiv := Equiv.Set.univPi X
  continuous_toFun := continuous_pi fun i =>
    Continuous.subtype_mk ((continuous_apply i).comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)) _

end F0701a6c

open F0701a6c in
open SocialEquilibrium.Existence in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (hX : ∀ i, IsPolyhedron (X i) ∧ IsContractible (X i)) :
    IsPolyhedron (Set.univ.pi X) ∧ IsContractible (Set.univ.pi X) := by
  classical
  refine ⟨?_, ?_⟩
  · choose m Q hQ e using fun i => (hX i).1
    let L : (∀ i, EuclideanSpace ℝ (Fin (m i))) ≃L[ℝ]
        EuclideanSpace ℝ (Fin (Module.finrank ℝ (∀ i, EuclideanSpace ℝ (Fin (m i))))) :=
      ContinuousLinearEquiv.ofFinrankEq (by simp)
    refine ⟨_, L.toLinearMap '' Set.univ.pi Q,
      geom_image L.toLinearMap (geom_pi Q hQ), ⟨?_⟩⟩
    exact (univPiHomeo X).trans ((Homeomorph.piCongrRight fun i => (e i).some).trans
      ((univPiHomeo Q).symm.trans ((L.toHomeomorph.image _).trans
        (Homeomorph.setCongr (by ext; simp)))))
  · choose z0 H hH0 hH1 using fun i => (hX i).2
    refine ⟨⟨fun i => z0 i, fun i _ => (z0 i).2⟩,
      ⟨fun p => ⟨fun i => (H i (p.1, ⟨p.2.1 i, p.2.2 i trivial⟩)).1, fun i _ => (H i _).2⟩,
        ?_⟩, ?_, ?_⟩
    · refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
      refine continuous_subtype_val.comp ((H i).continuous.comp
        (continuous_fst.prodMk (Continuous.subtype_mk ?_ _)))
      exact (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
    · intro z
      apply Subtype.ext
      funext i
      simp [hH0]
    · intro z
      apply Subtype.ext
      funext i
      simp [hH1]
