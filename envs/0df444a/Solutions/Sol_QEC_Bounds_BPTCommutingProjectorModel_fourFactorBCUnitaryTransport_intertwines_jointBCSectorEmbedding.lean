-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fourFactorBCUnitaryTransport_intertwines_jointBCSectorEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:38:34.598755+00:00
-- url     : https://prove2.me/submissions/f3309ca1-994d-4fe1-b658-7ecdb3bc1f93

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Core
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingLeft_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingRight_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorJointBCSectorEmbedding_apply_factor_through_middle
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorBCUnitaryTransport_middle_intertwines_jointBCSectorMiddleEmbedding
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_conjugateUnitaryTransport_apply
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


attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingLeft_apply_tmul
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingRight_apply_tmul

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
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (E : Semantics.UnitaryTransport (Semantics.CompositeSystem B C)
      (Semantics.CompositeSystem B C))
    (V : Semantics.UnitaryTransport (Semantics.CompositeSystem pB pC)
      (Semantics.CompositeSystem pB pC))
    (hintertwines : E.toLinearEquiv.toLinearMap.comp (submoduleTensorEmbedding pB pC).toLinearMap =
      (submoduleTensorEmbedding pB pC).toLinearMap.comp V.toLinearEquiv.toLinearMap) :
    (fourFactorBCUnitaryTransport (A := A) (D := D) E).toLinearEquiv.toLinearMap.comp
        (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC) =
      (fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC).comp
        (jointBCSectorActiveUnitary (A := A) pB pC V).toLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro vector
  change fourFactorBCUnitaryTransport E (fourFactorJointBCSectorEmbedding pB pC vector) =
    fourFactorJointBCSectorEmbedding pB pC (jointBCSectorActiveUnitary pB pC V vector)
  calc
    fourFactorBCUnitaryTransport E (fourFactorJointBCSectorEmbedding pB pC vector) =
        fourFactorBCUnitaryTransport E
          ((unitaryLTensor A (tensorAssociatorUnitary B C D).symm).symm
            (jointBCSectorMiddleEmbedding pB pC (jointBCSectorMiddleTransport pB pC vector))) := by
          rw [fourFactorJointBCSectorEmbedding_apply_factor_through_middle]
    _ = (unitaryLTensor A (tensorAssociatorUnitary B C D).symm).symm
          (unitaryLTensor A (unitaryRTensor E D)
            (jointBCSectorMiddleEmbedding pB pC (jointBCSectorMiddleTransport pB pC vector))) := by
          rw [fourFactorBCUnitaryTransport, conjugateUnitaryTransport_apply]
          simp
    _ = (unitaryLTensor A (tensorAssociatorUnitary B C D).symm).symm
          (jointBCSectorMiddleEmbedding pB pC
            (unitaryLTensor A (unitaryRTensor V D) (jointBCSectorMiddleTransport pB pC vector))) := by
          have hmiddle := congrArg
            (fun map => map (jointBCSectorMiddleTransport pB pC vector))
            (fourFactorBCUnitaryTransport_middle_intertwines_jointBCSectorMiddleEmbedding
              (A := A) (D := D) pB pC E V hintertwines)
          apply congrArg (unitaryLTensor A (tensorAssociatorUnitary B C D).symm).symm
          exact hmiddle
    _ = (unitaryLTensor A (tensorAssociatorUnitary B C D).symm).symm
          (jointBCSectorMiddleEmbedding pB pC
            (jointBCSectorMiddleTransport pB pC
              ((jointBCSectorMiddleTransport pB pC).symm
                (unitaryLTensor A (unitaryRTensor V D)
                  (jointBCSectorMiddleTransport pB pC vector))))) := by
          simp
    _ = fourFactorJointBCSectorEmbedding pB pC
          ((jointBCSectorMiddleTransport pB pC).symm
            (unitaryLTensor A (unitaryRTensor V D)
              (jointBCSectorMiddleTransport pB pC vector))) := by
          symm
          simpa using fourFactorJointBCSectorEmbedding_apply_factor_through_middle pB pC
            ((jointBCSectorMiddleTransport pB pC).symm
              (unitaryLTensor A (unitaryRTensor V D)
                (jointBCSectorMiddleTransport pB pC vector)))
    _ = fourFactorJointBCSectorEmbedding pB pC (jointBCSectorActiveUnitary pB pC V vector) := by
          rw [jointBCSectorActiveUnitary, conjugateUnitaryTransport_apply]
end QEC.Bounds.BPTCommutingProjectorModel
