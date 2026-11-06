-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_of_tensorMap_left_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:21:13.142207+00:00
-- url     : https://prove2.me/submissions/8aa8ea15-0f09-4fc0-9aa0-986cf9f10b78

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Embedding
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_rightTensorCompression_tensorMap_left
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
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (P : Semantics.Operator H) (eta : K) (heta : ‖eta‖ = 1)
    (h : (TensorProduct.map P (1 : Semantics.Operator K)).IsSymmetricProjection) :
    P.IsSymmetricProjection := by
  have hmapMul : TensorProduct.map (P * P) (1 : Semantics.Operator K) =
      TensorProduct.map P (1 : Semantics.Operator K) *
        TensorProduct.map P (1 : Semantics.Operator K) := by
    rw [← TensorProduct.map_mul]
    simp
  have hPidem : P * P = P := by
    calc
      P * P = rightTensorCompression eta
          (TensorProduct.map (P * P) (1 : Semantics.Operator K)) :=
        (rightTensorCompression_tensorMap_left (P * P) eta heta).symm
      _ = rightTensorCompression eta
          (TensorProduct.map P (1 : Semantics.Operator K) *
            TensorProduct.map P (1 : Semantics.Operator K)) :=
        congrArg (rightTensorCompression eta) hmapMul
      _ = rightTensorCompression eta (TensorProduct.map P (1 : Semantics.Operator K)) :=
        congrArg (rightTensorCompression eta) h.isIdempotentElem
      _ = P := rightTensorCompression_tensorMap_left P eta heta
  have hPadjoint : LinearMap.adjoint P = P := by
    calc
      LinearMap.adjoint P = rightTensorCompression eta
          (TensorProduct.map (LinearMap.adjoint P) (1 : Semantics.Operator K)) :=
        (rightTensorCompression_tensorMap_left (LinearMap.adjoint P) eta heta).symm
      _ = rightTensorCompression eta
          (LinearMap.adjoint (TensorProduct.map P (1 : Semantics.Operator K))) := by
        congr 1
        rw [TensorProduct.adjoint_map, LinearMap.adjoint_one]
      _ = rightTensorCompression eta (TensorProduct.map P (1 : Semantics.Operator K)) :=
        congrArg (rightTensorCompression eta) h.isSymmetric.adjoint_eq
      _ = P := rightTensorCompression_tensorMap_left P eta heta
  constructor
  · exact hPidem
  · exact (LinearMap.isSymmetric_iff_isSelfAdjoint P).mpr
      (LinearMap.isSelfAdjoint_iff'.mpr hPadjoint)
end QEC.Bounds.BPTCommutingProjectorModel
