-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P07.kification_closedEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T23:29:31.53773+00:00
-- url     : https://prove2.me/submissions/a8990ce1-fcd0-4823-8303-28f9dbefbd82

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_kification_isEmbedding_of_range_isKSpace
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_closedSubspace_isKSpace
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intakethird100.P07
noncomputable section

universe u v



open CategoryTheory Topology TopologicalSpace

/-- Lemma B.10, PDF p. 37: k preserves closed embeddings, for the same
underlying map, with final probe topologies on its domain and codomain. -/
theorem solution
    (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : IsClosedEmbedding f) :
    @IsClosedEmbedding (KSpace X) (KSpace Y) _ _ f := by
  letI : UCompactlyGeneratedSpace.{u} (KSpace Y) := kSpaceGenerated Y
  have hr : @IsClosed (KSpace Y) (kSpaceTopology Y) (Set.range f) :=
    hf.isClosed_range.preimage (kToOriginal (ContinuousMap.id Y)).continuous
  have hcg : UCompactlyGeneratedSpace.{u} {y : KSpace Y // y ∈ Set.range f} :=
    closedSubspace_isKSpace (KSpace Y) (Set.range f) hr
  exact ⟨kification_isEmbedding_of_range_isKSpace X Y f hf.isEmbedding hcg,hr⟩
