-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P07.kification_openEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T23:31:20.993554+00:00
-- url     : https://prove2.me/submissions/194161a0-de2c-4f52-92e5-af1710291fc9

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_kification_isEmbedding_of_range_isKSpace
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_openSubspace_isKSpace
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intakethird100.P07
noncomputable section

universe u v



open CategoryTheory Topology TopologicalSpace

/-- Lemma B.12, PDF p. 37: k preserves open embeddings, without a
separation hypothesis on either topological space. -/
theorem solution
    (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : IsOpenEmbedding f) :
    @IsOpenEmbedding (KSpace X) (KSpace Y) _ _ f := by
  letI : UCompactlyGeneratedSpace.{u} (KSpace Y) := kSpaceGenerated Y
  have hr : @IsOpen (KSpace Y) (kSpaceTopology Y) (Set.range f) :=
    hf.isOpen_range.preimage (kToOriginal (ContinuousMap.id Y)).continuous
  have hcg : UCompactlyGeneratedSpace.{u} {y : KSpace Y // y ∈ Set.range f} :=
    openSubspace_isKSpace (KSpace Y) (Set.range f) hr
  exact ⟨kification_isEmbedding_of_range_isKSpace X Y f hf.isEmbedding hcg,hr⟩
