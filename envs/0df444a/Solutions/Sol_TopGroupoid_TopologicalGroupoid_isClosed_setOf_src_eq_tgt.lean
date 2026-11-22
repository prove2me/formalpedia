-- Prove2me | solution 1 for TopGroupoid.TopologicalGroupoid.isClosed_setOf_src_eq_tgt
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T18:33:45.599371+00:00
-- url     : https://prove2.me/submissions/d5747a66-aec4-44c9-b46f-d3e8a5cead48

import Definitions.Def_TopGroupoid_TopologicalGroupoid
import Theorems.Thm_CGWH_isClosed_setOf_eq
import Theorems.Thm_CGWH_weaklyHausdorffSpace_subtype_and_compactlyGenerated

open Topology

set_option autoImplicit false

universe u

private theorem compactlyGenerated_closed_subspace {R : Type u} [TopologicalSpace R]
    [CompactlyGeneratedSpace R] {S : Set R} (hS : IsClosed S) :
    CompactlyGeneratedSpace S := by
  refine compactlyGeneratedSpace_of_isClosed fun A hA => ?_
  have hImage : IsClosed (Subtype.val '' A : Set R) := by
    refine CompactlyGeneratedSpace.isClosed' fun K _ _ _ f hf => ?_
    have hPre : IsClosed (f ⁻¹' S) := hS.preimage hf
    have : CompactSpace (f ⁻¹' S) := isCompact_iff_compactSpace.mp hPre.isCompact
    let g : (f ⁻¹' S) → S := fun x => ⟨f x, x.property⟩
    have hg : Continuous g := (hf.comp continuous_subtype_val).subtype_mk _
    have hEq : f ⁻¹' (Subtype.val '' A) = Subtype.val '' (g ⁻¹' A) := by
      ext x
      constructor
      · rintro ⟨y, hy, hval⟩
        have hx : f x ∈ S := hval ▸ y.property
        refine ⟨⟨x, hx⟩, ?_, rfl⟩
        change g ⟨x, hx⟩ ∈ A
        rwa [show g ⟨x, hx⟩ = y from Subtype.ext hval.symm]
      · rintro ⟨y, hy, rfl⟩
        exact ⟨g y, hy, rfl⟩
    rw [hEq]
    exact hPre.isClosedEmbedding_subtypeVal.isClosedMap _ (hA _ _ hg)
  simpa only [Set.preimage_image_eq _ Subtype.val_injective] using
    hImage.preimage (continuous_subtype_val : Continuous (Subtype.val : S → R))

theorem solution {X R : Type u} [TopologicalSpace X] [TopologicalSpace R]
    (G : TopGroupoid.TopologicalGroupoid X R) :
    IsClosed {g : R | G.src g = G.tgt g} ∧
      CompactlyGeneratedSpace {g : R // G.src g = G.tgt g} ∧
      CGWH.WeaklyHausdorffSpace {g : R // G.src g = G.tgt g} := by
  have := G.compactlyGeneratedSpace_arr
  have := G.weaklyHausdorffSpace_obj
  have := G.weaklyHausdorffSpace_arr
  have hClosed : IsClosed {g : R | G.src g = G.tgt g} :=
    CGWH.isClosed_setOf_eq G.continuous_src G.continuous_tgt
  exact ⟨hClosed, compactlyGenerated_closed_subspace hClosed,
    (CGWH.weaklyHausdorffSpace_subtype_and_compactlyGenerated R).1 _⟩
