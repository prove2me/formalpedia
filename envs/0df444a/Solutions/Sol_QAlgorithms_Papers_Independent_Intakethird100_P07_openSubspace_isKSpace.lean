-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P07.openSubspace_isKSpace
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T23:23:01.636192+00:00
-- url     : https://prove2.me/submissions/167070bc-fb3d-4d71-910c-f05630635a64

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07
import Mathlib.Topology.Compactness.LocallyCompact
set_option autoImplicit false
open CategoryTheory Topology TopologicalSpace
noncomputable section
universe u
namespace QAlgorithms.Papers.Independent.Intakethird100.P07
end QAlgorithms.Papers.Independent.Intakethird100.P07

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

open QAlgorithms.Papers.Independent.Intakethird100.P07

theorem solution (X : Type u) [TopologicalSpace X]
    [UCompactlyGeneratedSpace.{u} X] (A : Set X) (hA : IsOpen A) :
    UCompactlyGeneratedSpace.{u} A := by
  refine uCompactlyGeneratedSpace_of_isOpen (X := A) ?_
  intro s hs
  have him : IsOpen ((Subtype.val : A → X) '' s) := by
    apply UCompactlyGeneratedSpace.isOpen
    intro S f
    have hD : IsOpen (f ⁻¹' A) := hA.preimage f.continuous
    letI : CompactSpace S := @CompHaus.instCompactSpaceCarrierToTopTrue S
    letI : T2Space S := @CompHaus.instT2SpaceCarrierToTopTrue S
    letI : R1Space S := T2Space.r1Space
    letI : WeaklyLocallyCompactSpace S := instWeaklyLocallyCompactSpaceOfCompactSpace
    letI : LocallyCompactSpace S := WeaklyLocallyCompactSpace.locallyCompactSpace
    letI : LocallyCompactSpace (f ⁻¹' A) := hD.isLocallyClosed.locallyCompactSpace
    letI : T2Space (f ⁻¹' A) := instT2SpaceSubtype
    letI : WeaklyLocallyCompactSpace (f ⁻¹' A) := instWeaklyLocallyCompactSpaceOfLocallyCompactSpace
    letI : UCompactlyGeneratedSpace.{u} (f ⁻¹' A) := instCompactlyGeneratedSpaceOfWeaklyLocallyCompactSpace
    let g : C((f ⁻¹' A : Set S),A) :=
      ⟨fun x => ⟨f x.val,x.property⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
    have hg : IsOpen (g ⁻¹' s) := by
      apply UCompactlyGeneratedSpace.isOpen
      intro T q
      exact hs T (g.comp q)
    have heq : (Subtype.val : (f ⁻¹' A : Set S) → S) '' (g ⁻¹' s) =
        f ⁻¹' ((Subtype.val : A → X) '' s) := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact ⟨g y,hy,rfl⟩
      · rintro ⟨y,hy,he⟩
        have hx : f x ∈ A := he ▸ y.property
        refine ⟨⟨x,hx⟩,?_,rfl⟩
        have hh : g ⟨x,hx⟩ = y := Subtype.ext he.symm
        change g ⟨x,hx⟩ ∈ s
        rw [hh]
        exact hy
    rw [← heq]
    exact hD.isOpenMap_subtype_val (g ⁻¹' s) hg
  have hpre : (Subtype.val : A → X) ⁻¹' ((Subtype.val : A → X) '' s) = s :=
    Set.preimage_image_eq _ Subtype.val_injective
  rw [← hpre]
  exact him.preimage continuous_subtype_val
