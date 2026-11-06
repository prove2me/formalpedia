-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.extend_union_rankOne_eq_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:44:05.133012+00:00
-- url     : https://prove2.me/submissions/d6d67ed2-f326-4c25-a160-b083f8f79efb

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Support
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorization
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_abcFactorization_conj_extend_left
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_abcFactorization_conj_extend_right
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_abcFactorization_conj_extend_union_rankOne
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorizationWithReference_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceReordering_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceTransport_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.mem_regionSubsystem_selected_iff
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.regionSubsystem_selected
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.logMatrix_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.registerFactorizationWithReference_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceReordering_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceTransport_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hdisjoint : Disjoint left right)
    (labels labels' : Semantics.Qudit.Label
      (M.regionSubsystem (left ∪ right)).selectedDimensions) :
    let A := M.regionSubsystem left
    let B := M.regionSubsystem right
    let R := M.regionSubsystem (left ∪ right)
    let hAB : Disjoint A.selected B.selected := by
      simpa [A, B] using hdisjoint
    let leftLabels := (M.splitUnionSelectedLabel left right labels).1
    let rightLabels := (M.splitUnionSelectedLabel left right labels).2
    let leftLabels' := (M.splitUnionSelectedLabel left right labels').1
    let rightLabels' := (M.splitUnionSelectedLabel left right labels').2
    R.extendLocalToRegister
      (InnerProductSpace.rankOne Complex
        (EuclideanSpace.basisFun (Semantics.Qudit.Label R.selectedDimensions) Complex labels)
        (EuclideanSpace.basisFun (Semantics.Qudit.Label R.selectedDimensions)
          Complex labels')).toLinearMap =
      A.extendLocalToRegister
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Semantics.Qudit.Label A.selectedDimensions)
            Complex leftLabels)
          (EuclideanSpace.basisFun (Semantics.Qudit.Label A.selectedDimensions)
            Complex leftLabels')).toLinearMap *
      B.extendLocalToRegister
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Semantics.Qudit.Label B.selectedDimensions)
            Complex rightLabels)
          (EuclideanSpace.basisFun (Semantics.Qudit.Label B.selectedDimensions)
            Complex rightLabels')).toLinearMap := by
  dsimp
  let A := M.regionSubsystem left
  let B := M.regionSubsystem right
  let R := M.regionSubsystem (left ∪ right)
  let C := BPTEntropy.QuditSubsystem.unionSubsystem A B
  let U := BPTEntropy.QuditSubsystem.abcFactorization A B (by
    simpa [A, B] using hdisjoint)
  let leftUnit := (InnerProductSpace.rankOne Complex
    (EuclideanSpace.basisFun (Semantics.Qudit.Label A.selectedDimensions) Complex
      (M.splitUnionSelectedLabel left right labels).1)
    (EuclideanSpace.basisFun (Semantics.Qudit.Label A.selectedDimensions) Complex
      (M.splitUnionSelectedLabel left right labels').1)).toLinearMap
  let rightUnit := (InnerProductSpace.rankOne Complex
    (EuclideanSpace.basisFun (Semantics.Qudit.Label B.selectedDimensions) Complex
      (M.splitUnionSelectedLabel left right labels).2)
    (EuclideanSpace.basisFun (Semantics.Qudit.Label B.selectedDimensions) Complex
      (M.splitUnionSelectedLabel left right labels').2)).toLinearMap
  let unionUnit := (InnerProductSpace.rankOne Complex
    (EuclideanSpace.basisFun (Semantics.Qudit.Label R.selectedDimensions) Complex labels)
    (EuclideanSpace.basisFun (Semantics.Qudit.Label R.selectedDimensions)
      Complex labels')).toLinearMap
  let target : Semantics.Operator
      (Semantics.CompositeSystem A.selectedSystem
        (Semantics.CompositeSystem B.selectedSystem C.complementSystem)) :=
    TensorProduct.map leftUnit
      (TensorProduct.map rightUnit (1 : Semantics.Operator C.complementSystem))
  have hunion : U.conjOperator (R.extendLocalToRegister unionUnit) = target := by
    simpa [U, target, unionUnit, leftUnit, rightUnit] using
      M.abcFactorization_conj_extend_union_rankOne left right hdisjoint labels labels'
  have hproduct : U.conjOperator
      (A.extendLocalToRegister leftUnit * B.extendLocalToRegister rightUnit) = target := by
    rw [Semantics.UnitaryTransport.conjOperator_mul]
    rw [M.abcFactorization_conj_extend_left left right hdisjoint]
    rw [M.abcFactorization_conj_extend_right left right hdisjoint]
    change
      TensorProduct.map leftUnit
        (1 : Semantics.Operator (Semantics.CompositeSystem B.selectedSystem C.complementSystem)) *
        TensorProduct.map (1 : Semantics.Operator A.selectedSystem)
          (TensorProduct.map rightUnit (1 : Semantics.Operator C.complementSystem)) = target
    rw [show (1 : Semantics.Operator (Semantics.CompositeSystem B.selectedSystem
      C.complementSystem)) = TensorProduct.map
        (1 : Semantics.Operator B.selectedSystem)
        (1 : Semantics.Operator C.complementSystem) by
      symm
      exact TensorProduct.map_one]
    rw [← TensorProduct.map_mul, ← TensorProduct.map_mul]
    simp [target]
  calc
    R.extendLocalToRegister unionUnit = U.symm.conjOperator
        (U.conjOperator (R.extendLocalToRegister unionUnit)) :=
      (U.symm_conjOperator_conjOperator _).symm
    _ = U.symm.conjOperator target := by rw [hunion]
    _ = U.symm.conjOperator
        (U.conjOperator (A.extendLocalToRegister leftUnit *
          B.extendLocalToRegister rightUnit)) := by rw [hproduct]
    _ = A.extendLocalToRegister leftUnit * B.extendLocalToRegister rightUnit :=
      U.symm_conjOperator_conjOperator _
end QEC.Bounds.BPTCommutingProjectorModel
