-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P32.allCompactSubsets_isCGCover
-- status  : ACCEPTED   (prove)
-- author  : @21604
-- created : 2026-11-03T00:16:37.501485+00:00
-- url     : https://prove2.me/submissions/c69af367-7e1b-4643-bd87-1b87c47b8e80

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P32

open Set Topology
open QAlgorithms.Papers.Independent.Intakethird100.P32

universe u

/-- Corollary 3.1, PDF p.18: the inclusion family of all compact subsets covers
any CGH space in the CG topology, including the empty space.

For a compact `K`, the one-member family `{K}` suffices: `K ∩ K = K` is open in `K`,
so every point of `K` lies in the relative interior of the member indexed by `K`. -/
theorem solution (X : Type u) [TopologicalSpace X]
    [T2Space X] [CompactlyGeneratedSpace X] : CGCover (allCompactSubsets X) := by
  intro K hK
  classical
  refine ⟨{⟨K, hK⟩}, fun x => ?_⟩
  refine ⟨⟨K, hK⟩, Finset.mem_singleton_self _, ?_⟩
  have hpre : ((Subtype.val : K → X) ⁻¹' (allCompactSubsets X ⟨K, hK⟩)) = Set.univ := by
    ext y
    simp [allCompactSubsets]
  rw [hpre, interior_univ]
  exact Set.mem_univ x
