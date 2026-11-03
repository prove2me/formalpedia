-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P32.openCover_isCGCover
-- status  : ACCEPTED   (prove)
-- author  : @21604
-- created : 2026-11-03T00:14:12.54336+00:00
-- url     : https://prove2.me/submissions/482de8f6-5cec-49e9-b0c8-e9204f881d35

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P32

open Set Topology
open QAlgorithms.Papers.Independent.Intakethird100.P32

universe u

/-- Proposition 3.2, PDF p.18: every open cover of a CGH space is a CG-cover.

An open cover `U` is a CG-cover: given a compact `K`, each point of `K` lies in some `U a`,
so by compactness finitely many members `U a`, `a ∈ t`, cover `K`. Since each `U a` is open in
`X`, the relative set `K ∩ U a` is open in the compact space `K`, and hence every point of it
lies in its relative interior. -/
theorem solution (X : Type u) [TopologicalSpace X]
    [T2Space X] [CompactlyGeneratedSpace X] {A : Type u} (U : A → Set X)
    (hU : IsOpenCover U) : CGCover U := by
  intro K hK
  classical
  have hcov : K ⊆ ⋃ a, U a := fun x _ => Set.mem_iUnion.2 (hU.2 x)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU.1 hcov
  refine ⟨t, fun x => ?_⟩
  obtain ⟨a, hat, hax⟩ := Set.mem_iUnion₂.1 (ht x.2)
  refine ⟨a, hat, ?_⟩
  have hopen : IsOpen ((Subtype.val : K → X) ⁻¹' U a) :=
    (hU.1 a).preimage continuous_subtype_val
  rw [hopen.interior_eq]
  exact hax
