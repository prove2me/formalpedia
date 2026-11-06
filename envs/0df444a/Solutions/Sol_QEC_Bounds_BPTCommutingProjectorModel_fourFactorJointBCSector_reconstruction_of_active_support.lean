-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fourFactorJointBCSector_reconstruction_of_active_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:42:31.048203+00:00
-- url     : https://prove2.me/submissions/2043d2ac-48f0-4239-8455-5d0c0ddaa91e

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Regrouping
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_productBlockRegrouping_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_productBlockRegrouping_apply_tmul_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactor_sectorProjectorProduct_eq_jointBCSectorEmbedding_comp_adjoint
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_embedding_compression_of_right_absorption
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingLeft_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingRight_apply_tmul
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
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingLeft_apply_tmul
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingRight_apply_tmul
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


attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.productBlockRegrouping_apply_tmul
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.productBlockRegrouping_apply_tmul_tmul

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
    (P4 : Semantics.Operator
      (Semantics.CompositeSystem A (Semantics.CompositeSystem B (Semantics.CompositeSystem C D))))
    (hP4 : P4.IsSymmetricProjection)
    (hactive :
      P4 *
          TensorProduct.map (1 : Semantics.Operator A)
            (TensorProduct.map pB.starProjection.toLinearMap
              (TensorProduct.map (1 : Semantics.Operator C) (1 : Semantics.Operator D))) *
          TensorProduct.map (1 : Semantics.Operator A)
            (TensorProduct.map (1 : Semantics.Operator B)
              (TensorProduct.map pC.starProjection.toLinearMap
                (1 : Semantics.Operator D))) = P4) :
    let J := fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC
    P4 = J.comp (((LinearMap.adjoint J).comp (P4.comp J)).comp (LinearMap.adjoint J)) := by
  dsimp
  let J := fourFactorJointBCSectorEmbedding (A := A) (D := D) pB pC
  let E := J.comp (LinearMap.adjoint J)
  let LB : Semantics.Operator
      (Semantics.CompositeSystem A (Semantics.CompositeSystem B (Semantics.CompositeSystem C D))) :=
    TensorProduct.map (1 : Semantics.Operator A)
      (TensorProduct.map pB.starProjection.toLinearMap
        (TensorProduct.map (1 : Semantics.Operator C) (1 : Semantics.Operator D)))
  let LC : Semantics.Operator
      (Semantics.CompositeSystem A (Semantics.CompositeSystem B (Semantics.CompositeSystem C D))) :=
    TensorProduct.map (1 : Semantics.Operator A)
      (TensorProduct.map (1 : Semantics.Operator B)
        (TensorProduct.map pC.starProjection.toLinearMap (1 : Semantics.Operator D)))
  have hsectorProduct : LB * LC = E := by
    simpa [LB, LC, E, J] using
      (fourFactor_sectorProjectorProduct_eq_jointBCSectorEmbedding_comp_adjoint
        (A := A) (D := D) pB pC)
  have hright : P4 * E = P4 := by
    calc
      P4 * E = P4 * (LB * LC) := by rw [hsectorProduct]
      _ = P4 * LB * LC := (mul_assoc P4 LB LC).symm
      _ = P4 := by simpa [LB, LC] using hactive
  have hP4self : LinearMap.adjoint P4 = P4 := hP4.isSymmetric.adjoint_eq
  have hEself : LinearMap.adjoint E = E := by
    dsimp only [E]
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
  have hleft : E * P4 = P4 := by
    have hadjoint := congrArg LinearMap.adjoint hright
    change LinearMap.adjoint (P4.comp E) = LinearMap.adjoint P4 at hadjoint
    rw [LinearMap.adjoint_comp, hP4self, hEself] at hadjoint
    simpa [Module.End.mul_eq_comp] using hadjoint
  have hcommute : Commute P4 E := hright.trans hleft.symm
  exact embedding_compression_of_right_absorption J P4 hcommute hright
end QEC.Bounds.BPTCommutingProjectorModel
