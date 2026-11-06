-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.abcFactorization_conj_extend_union_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:39:57.610195+00:00
-- url     : https://prove2.me/submissions/ce76e51a-a2cb-4d1c-b660-27a3d199a08e

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Support
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorization
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unionSelectedFactorization_apply_basis
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_abcFactorization_eq_union_factorization
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_composeUnitaryTransport_conjOperator
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_registerFactorization_conj_extendLocalToRegister
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_conj_tensorMap
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryRTensor_conj_tensorMap_left
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
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
set_option maxHeartbeats 4000000
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
    let C := BPTEntropy.QuditSubsystem.unionSubsystem A B
    let leftLabels := (M.splitUnionSelectedLabel left right labels).1
    let rightLabels := (M.splitUnionSelectedLabel left right labels).2
    let leftLabels' := (M.splitUnionSelectedLabel left right labels').1
    let rightLabels' := (M.splitUnionSelectedLabel left right labels').2
    (BPTEntropy.QuditSubsystem.abcFactorization A B hAB).conjOperator
      (R.extendLocalToRegister
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Semantics.Qudit.Label R.selectedDimensions) Complex labels)
          (EuclideanSpace.basisFun (Semantics.Qudit.Label R.selectedDimensions)
            Complex labels')).toLinearMap) =
      TensorProduct.map
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Semantics.Qudit.Label A.selectedDimensions)
            Complex leftLabels)
          (EuclideanSpace.basisFun (Semantics.Qudit.Label A.selectedDimensions)
            Complex leftLabels')).toLinearMap
        (TensorProduct.map
          (InnerProductSpace.rankOne Complex
            (EuclideanSpace.basisFun (Semantics.Qudit.Label B.selectedDimensions)
              Complex rightLabels)
            (EuclideanSpace.basisFun (Semantics.Qudit.Label B.selectedDimensions)
              Complex rightLabels')).toLinearMap
          (1 : Semantics.Operator C.complementSystem)) := by
  dsimp
  let A := M.regionSubsystem left
  let B := M.regionSubsystem right
  let R := M.regionSubsystem (left ∪ right)
  let C := BPTEntropy.QuditSubsystem.unionSubsystem A B
  have hAB : Disjoint A.selected B.selected := by
    simpa [A, B] using hdisjoint
  have htransport :
      (unitaryRTensor (M.unionSelectedFactorization left right hdisjoint)
        (BPTEntropy.QuditSubsystem.unionSubsystem
          (M.regionSubsystem left) (M.regionSubsystem right)).complementSystem).conjOperator
        (TensorProduct.map
          (InnerProductSpace.rankOne Complex
            (EuclideanSpace.basisFun
              (Semantics.Qudit.Label (M.regionSubsystem (left ∪ right)).selectedDimensions)
              Complex labels)
            (EuclideanSpace.basisFun
              (Semantics.Qudit.Label (M.regionSubsystem (left ∪ right)).selectedDimensions)
              Complex labels')).toLinearMap
          (1 : Semantics.Operator
            (BPTEntropy.QuditSubsystem.unionSubsystem
              (M.regionSubsystem left) (M.regionSubsystem right)).complementSystem)) =
        TensorProduct.map
          ((M.unionSelectedFactorization left right hdisjoint).conjOperator
            (InnerProductSpace.rankOne Complex
              (EuclideanSpace.basisFun
                (Semantics.Qudit.Label (M.regionSubsystem (left ∪ right)).selectedDimensions)
                Complex labels)
              (EuclideanSpace.basisFun
                (Semantics.Qudit.Label (M.regionSubsystem (left ∪ right)).selectedDimensions)
                Complex labels')).toLinearMap)
          (1 : Semantics.Operator
            (BPTEntropy.QuditSubsystem.unionSubsystem
              (M.regionSubsystem left) (M.regionSubsystem right)).complementSystem) := by
    exact unitaryRTensor_conj_tensorMap_left
      (M.unionSelectedFactorization left right hdisjoint)
        (BPTEntropy.QuditSubsystem.unionSubsystem
          (M.regionSubsystem left) (M.regionSubsystem right)).complementSystem _
  rw [M.abcFactorization_eq_union_factorization left right hdisjoint]
  erw [composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator]
  rw [registerFactorization_conj_extendLocalToRegister]
  refine (congrArg
    (tensorAssociatorUnitary A.selectedSystem B.selectedSystem C.complementSystem).conjOperator
    htransport).trans ?_
  rw [Semantics.QuditSubsystem.conjOperator_rankOne]
  rw [M.unionSelectedFactorization_apply_basis left right hdisjoint labels,
    M.unionSelectedFactorization_apply_basis left right hdisjoint labels']
  rw [← Semantics.DensityOperator.tensorMap_rankOne]
  exact tensorAssociatorUnitary_conj_tensorMap _ _ _
end QEC.Bounds.BPTCommutingProjectorModel
