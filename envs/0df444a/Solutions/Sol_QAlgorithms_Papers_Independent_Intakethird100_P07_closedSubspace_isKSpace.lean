-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P07.closedSubspace_isKSpace
-- status  : ACCEPTED   (prove)
-- author  : @21604
-- created : 2026-11-05T10:53:06.265535+00:00
-- url     : https://prove2.me/submissions/5f791181-5554-4701-a0d3-4e932dd41f75

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07

noncomputable section

universe u

open CategoryTheory Topology TopologicalSpace
open QAlgorithms.Papers.Independent.Intakethird100.P07

/-- Theorem B.9 (de Groote, Observables I, pp. 36–37). Every closed subspace of a k-space is a
k-space; no Hausdorff axiom is needed on the ambient space.

Using the characterisation of `UCompactlyGeneratedSpace` by closed sets that are closed after
pulling back along every compact Hausdorff probe, it suffices to check closedness in `X`. A set
`s ⊆ A` is closed in `A` iff its image in `X` is closed (`A` is closed, so the inclusion is a
closed embedding). For a probe `f : S → X`, the preimage `f ⁻¹' A` is a closed, hence compact
Hausdorff subspace of `S`; restricting `f` to it and using the hypothesis on those restricted
probes shows `f ⁻¹' (image of s)` is closed. -/
theorem solution (X : Type u) [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X]
    (A : Set X) (hA : IsClosed A) : UCompactlyGeneratedSpace.{u} A := by
  refine uCompactlyGeneratedSpace_of_isClosed (X := A) ?_
  intro s hs
  -- closedness in the closed subspace `A` is closedness of the image in `X`
  have hclosed_iff : IsClosed s ↔ IsClosed ((Subtype.val : A → X) '' s) := by
    constructor
    · intro hs'
      exact hA.isClosedMap_subtype_val s hs'
    · intro hs'
      have hpre : (Subtype.val : A → X) ⁻¹' ((Subtype.val : A → X) '' s) = s := by
        ext x
        constructor
        · rintro ⟨y, hy, hyx⟩
          have : y = x := Subtype.ext hyx
          simpa [this] using hy
        · intro hx
          exact ⟨x, hx, rfl⟩
      rw [← hpre]
      exact hs'.preimage continuous_subtype_val
  rw [hclosed_iff]
  refine UCompactlyGeneratedSpace.isClosed (X := X) (s := (Subtype.val : A → X) '' s) ?_
  intro S f
  have hTclosed : IsClosed (f ⁻¹' A) := hA.preimage f.continuous
  have hcs : CompactSpace (f ⁻¹' A) := isCompact_iff_compactSpace.1 hTclosed.isCompact
  -- restrict the probe to the compact Hausdorff preimage of `A`
  let g : C((f ⁻¹' A : Set S), A) :=
    ⟨fun x => ⟨f x.1, x.2⟩, Continuous.subtype_mk (f.continuous.comp continuous_subtype_val) _⟩
  have hgs : IsClosed (g ⁻¹' s) := hs (@CompHaus.of (f ⁻¹' A) inferInstance hcs inferInstance) g
  have himg : (Subtype.val : (f ⁻¹' A : Set S) → S) '' (g ⁻¹' s) =
      f ⁻¹' ((Subtype.val : A → X) '' s) := by
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hx : x = y.val := hyx.symm
      rw [hx]
      exact ⟨⟨f y.1, y.2⟩, by simpa [g] using hy, rfl⟩
    · rintro ⟨a, ha, hax⟩
      have hxT : x ∈ f ⁻¹' A := by
        rw [Set.mem_preimage, ← hax]
        exact a.2
      refine ⟨⟨x, hxT⟩, ?_, rfl⟩
      show g ⟨x, hxT⟩ ∈ s
      have hga : g ⟨x, hxT⟩ = a := Subtype.ext hax.symm
      rwa [hga]
  have himgclosed : IsClosed ((Subtype.val : (f ⁻¹' A : Set S) → S) '' (g ⁻¹' s)) :=
    hTclosed.isClosedMap_subtype_val (g ⁻¹' s) hgs
  rwa [himg] at himgclosed

end
