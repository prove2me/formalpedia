-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P94.bundle_trivializingOpenCover
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T19:27:58.425475+00:00
-- url     : https://prove2.me/submissions/5a91f604-7079-4a4c-95ab-6cefd68c4ca8

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P94

open Set Filter Topology Bundle

open QAlgorithms.Papers.Independent.Gap48.P05

universe u v w z

section BundleResults

variable {K : Type u} [RCLike K]

variable {Z : Type v} [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]

variable [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z]

variable [LocallyConvexSpace ℝ Z] [T2Space Z]

variable {X : Type w} [TopologicalSpace X] [T2Space X] [ChartedSpace Z X]

variable {F : Type z} [TopologicalSpace F] [AddCommGroup F]

variable [Module K F] [Module ℝ F] [IsScalarTower ℝ K F]

variable [IsTopologicalAddGroup F] [ContinuousSMul K F] [ContinuousSMul ℝ F]

variable [LocallyConvexSpace ℝ F] [T2Space F]

variable {V : X → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module K (V x)]

variable [∀ x, TopologicalSpace (V x)]

variable [TopologicalSpace (TotalSpace F V)] [T2Space (TotalSpace F V)]

variable [FiberBundle F V]

open QAlgorithms.Papers.Independent.Intake100.P94 in
theorem solution
    (r : WithTop ℕ) (B : LCVectorBundle r K Z X F V)
    [FiniteDimensional ℝ Z] [SigmaCompactSpace X] :
    ∃ P : Set (Set X),
      (∀ U ∈ P, IsOpen U) ∧ Set.sUnion P = Set.univ ∧
      ∀ U ∈ P, ∃ e : Trivialization F (Bundle.TotalSpace.proj : TotalSpace F V → X),
        e ∈ trivializationAtlas F V ∧ e.baseSet = U := by
  refine ⟨{U | ∃ e : Trivialization F (Bundle.TotalSpace.proj : TotalSpace F V → X),
      e ∈ trivializationAtlas F V ∧ e.baseSet = U}, ?_, ?_, ?_⟩
  · rintro U ⟨e, _, rfl⟩
    exact e.open_baseSet
  · ext x
    simp only [Set.mem_sUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨_, ⟨trivializationAt F V x, trivialization_mem_atlas F V x, rfl⟩,
      mem_baseSet_trivializationAt F V x⟩
  · intro U hU
    exact hU

end BundleResults
