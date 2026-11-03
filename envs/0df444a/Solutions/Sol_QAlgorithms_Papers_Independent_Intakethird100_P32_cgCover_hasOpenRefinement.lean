-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P32.cgCover_hasOpenRefinement
-- status  : ACCEPTED   (prove)
-- author  : @21604
-- created : 2026-11-03T00:22:16.164881+00:00
-- url     : https://prove2.me/submissions/b5065afa-7c0e-4f35-a0ef-44982e99418d

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P32

open Set Topology
open QAlgorithms.Papers.Independent.Intakethird100.P32

universe u

/-- Proposition 3.3, PDF p.18: every CG-cover of a locally compact Hausdorff space admits an open
refinement; the interiors of the members give a canonical such refinement.

Fix `x`. Local compactness gives a compact neighbourhood `K` of `x`. Apply the CG-cover property
to `K`: some member `V a` meets `K` in a set that contains an `x`-neighbourhood *relative to `K`*.
Concretely, `interior_K ((↑) ⁻¹' V a)` is open in the subspace `K` and contains `x`, so by the
description of neighbourhoods in a subspace there is a neighbourhood `u` of `x` in `X` with
`K ∩ u ⊆ V a`. Intersecting `u` with the open set `interior K` produces an open neighbourhood of
`x` in `X` contained in `V a`, i.e. `x ∈ interior (V a)`. -/
theorem solution (X : Type u) [TopologicalSpace X]
    [T2Space X] [CompactlyGeneratedSpace X] [LocallyCompactSpace X]
    {A : Type u} (V : A → Set X) (hV : CGCover V) :
    HasOpenRefinement V := by
  intro x
  obtain ⟨K, hKc, hKnhds⟩ := exists_compact_mem_nhds x
  have hxK : x ∈ K := mem_of_mem_nhds hKnhds
  obtain ⟨J, hJ⟩ := hV K hKc
  obtain ⟨a, _haJ, hxint⟩ := hJ ⟨x, hxK⟩
  refine ⟨a, ?_⟩
  -- work in the relative interior inside the compact subspace `K`
  rw [mem_interior] at hxint
  obtain ⟨O, hOsub, hOopen, hxO⟩ := hxint
  have hOnhds : O ∈ 𝓝 (⟨x, hxK⟩ : K) := hOopen.mem_nhds hxO
  rw [mem_nhds_subtype] at hOnhds
  obtain ⟨u, hu, husub⟩ := hOnhds
  -- shrink the neighbourhood `u` to an open one
  obtain ⟨v, hvsub, hvopen, hxv⟩ := mem_nhds_iff.1 hu
  -- `K` is a neighbourhood of `x`, hence `x` lies in its interior
  obtain ⟨w, hwsub, hwopen, hxw⟩ := mem_nhds_iff.1 hKnhds
  have hxintK : x ∈ interior K := mem_interior.2 ⟨w, hwsub, hwopen, hxw⟩
  refine mem_interior.2 ⟨v ∩ interior K, ?_, hvopen.inter isOpen_interior, ⟨hxv, hxintK⟩⟩
  rintro y ⟨hyv, hyK⟩
  have hyK' : y ∈ K := interior_subset hyK
  have hmem : (⟨y, hyK'⟩ : K) ∈ (Subtype.val : K → X) ⁻¹' u := hvsub hyv
  exact hOsub (husub hmem)
