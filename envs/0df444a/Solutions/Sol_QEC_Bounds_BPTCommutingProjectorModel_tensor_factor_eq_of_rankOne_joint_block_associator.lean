-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.tensor_factor_eq_of_rankOne_joint_block_associator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:25:41.511775+00:00
-- url     : https://prove2.me/submissions/94d4053d-43b8-4d83-835f-13058a44040a

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ExternalResidual
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Tensor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftTensorCompression_tensorMap
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftTensorCompression_tensorAssociator_conj_tensorMap
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftInteractionCoefficient_unitaryLTensor_conjOperator
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
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (phi : A) (hphi : ‖phi‖ = 1)
    (Pleft : Semantics.Operator (Semantics.CompositeSystem A (Semantics.CompositeSystem B C)))
    (Qright : Semantics.Operator (Semantics.CompositeSystem B (Semantics.CompositeSystem C D)))
    (P_D : Semantics.Operator D)
    (hjoint :
      (unitaryLTensor A (tensorAssociatorUnitary B C D).symm).conjOperator
          (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qright) =
        (tensorAssociatorUnitary A (Semantics.CompositeSystem B C) D).conjOperator
          (TensorProduct.map Pleft P_D)) :
    (tensorAssociatorUnitary B C D).symm.conjOperator Qright =
      TensorProduct.map (leftTensorCompression phi Pleft) P_D := by
  have hcompressed := congrArg (leftTensorCompression phi) hjoint
  have hleftTransport :
      leftTensorCompression phi
          ((unitaryLTensor A (tensorAssociatorUnitary B C D).symm).conjOperator
            (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qright)) =
        (tensorAssociatorUnitary B C D).symm.conjOperator
          (leftTensorCompression phi
            (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qright)) := by
    exact
      (leftInteractionCoefficient_unitaryLTensor_conjOperator
        (tensorAssociatorUnitary B C D).symm
        (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qright)
        phi phi)
  have hphiInner : inner Complex phi phi = 1 := by
    rw [inner_self_eq_norm_sq_to_K]
    simpa [hphi]
  have hrankApply :
      (InnerProductSpace.rankOne Complex phi phi).toLinearMap phi = phi := by
    simp [InnerProductSpace.rankOne_apply, hphi]
  have hrank :
      leftTensorCompression phi
          (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qright) =
        Qright := by
    rw [leftTensorCompression_tensorMap, hrankApply, hphiInner, one_smul]
  calc
    (tensorAssociatorUnitary B C D).symm.conjOperator Qright =
        (tensorAssociatorUnitary B C D).symm.conjOperator
          (leftTensorCompression phi
            (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qright)) := by
          rw [hrank]
    _ = leftTensorCompression phi
          ((unitaryLTensor A (tensorAssociatorUnitary B C D).symm).conjOperator
            (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Qright)) :=
          hleftTransport.symm
    _ = leftTensorCompression phi
          ((tensorAssociatorUnitary A (Semantics.CompositeSystem B C) D).conjOperator
            (TensorProduct.map Pleft P_D)) := hcompressed
    _ = TensorProduct.map (leftTensorCompression phi Pleft) P_D :=
          leftTensorCompression_tensorAssociator_conj_tensorMap phi Pleft P_D
end QEC.Bounds.BPTCommutingProjectorModel
