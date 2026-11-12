-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P94.whitneyDomain_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T19:36:42.113572+00:00
-- url     : https://prove2.me/submissions/02a13857-92ee-4ef8-a3e0-8a11068abb10

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

variable {F2 : Type*} [TopologicalSpace F2] [AddCommGroup F2]

variable [Module K F2] [Module ℝ F2] [IsScalarTower ℝ K F2]

variable [IsTopologicalAddGroup F2] [ContinuousSMul K F2] [ContinuousSMul ℝ F2]

variable [LocallyConvexSpace ℝ F2] [T2Space F2]

variable {V2 : X → Type*} [∀ x, AddCommGroup (V2 x)] [∀ x, Module K (V2 x)]

variable [∀ x, TopologicalSpace (V2 x)]

variable [TopologicalSpace (TotalSpace F2 V2)] [T2Space (TotalSpace F2 V2)]

variable [FiberBundle F2 V2]


open QAlgorithms.Papers.Independent.Intake100.P94 in
theorem solution
    (r : WithTop ℕ) (B1 : LCVectorBundle r K Z X F V)
    (B2 : LCVectorBundle r K Z X F2 V2)
    (U : Set (TotalSpace F V)) (hU : IsOpen U) :
    IsOpen (OpenWhitneyDomain (F2 := F2) (V2 := V2) U) := by
  exact hU.preimage (continuous_fst.comp continuous_subtype_val)

end BundleResults


