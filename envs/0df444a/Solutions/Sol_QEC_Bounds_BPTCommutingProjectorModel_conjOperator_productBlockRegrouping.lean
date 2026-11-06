-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.conjOperator_productBlockRegrouping
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:05:06.060092+00:00
-- url     : https://prove2.me/submissions/db53e66f-82c7-4cc7-b234-63743461c253

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Regrouping
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_productBlockRegrouping_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_productBlockRegrouping_apply_tmul_tmul
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
import Theorems.Thm_QEC_Semantics_QuditSubsystem_linearMap_ext_of_rankOne_basis
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
set_option maxHeartbeats 800000
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    {A W N X D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (phi : Semantics.CompositeSystem A W) (n0 : N) (c0 : X) (P_D : Semantics.Operator D) :
    productBlockRegrouping.conjOperator
      (TensorProduct.map
        (TensorProduct.map
          (InnerProductSpace.rankOne Complex phi phi).toLinearMap
          (InnerProductSpace.rankOne Complex
            (n0 ⊗ₜ[Complex] c0) (n0 ⊗ₜ[Complex] c0)).toLinearMap)
        P_D) =
      TensorProduct.map
        (InnerProductSpace.rankOne Complex
          (phi ⊗ₜ[Complex] n0) (phi ⊗ₜ[Complex] n0)).toLinearMap
        (TensorProduct.map (InnerProductSpace.rankOne Complex c0 c0).toLinearMap P_D) := by
  classical
  let Phi : Semantics.Operator D →ₗ[Complex]
      Semantics.Operator (Semantics.CompositeSystem
        (Semantics.CompositeSystem (Semantics.CompositeSystem A W) N)
          (Semantics.CompositeSystem X D)) :=
    { toFun := fun P =>
        productBlockRegrouping.conjOperator
          (TensorProduct.map
            (TensorProduct.map
              (InnerProductSpace.rankOne Complex phi phi).toLinearMap
              (InnerProductSpace.rankOne Complex
                (n0 ⊗ₜ[Complex] c0) (n0 ⊗ₜ[Complex] c0)).toLinearMap)
            P)
      map_add' := by
        intro P Q
        rw [TensorProduct.map_add_right]
        exact productBlockRegrouping.conjOperatorLinearMap.map_add
          (TensorProduct.map
            (TensorProduct.map
              (InnerProductSpace.rankOne Complex phi phi).toLinearMap
              (InnerProductSpace.rankOne Complex
                (n0 ⊗ₜ[Complex] c0) (n0 ⊗ₜ[Complex] c0)).toLinearMap)
            P)
          (TensorProduct.map
            (TensorProduct.map
              (InnerProductSpace.rankOne Complex phi phi).toLinearMap
              (InnerProductSpace.rankOne Complex
                (n0 ⊗ₜ[Complex] c0) (n0 ⊗ₜ[Complex] c0)).toLinearMap)
            Q)
      map_smul' := by
        intro a P
        rw [TensorProduct.map_smul_right]
        exact productBlockRegrouping.conjOperatorLinearMap.map_smul a
          (TensorProduct.map
            (TensorProduct.map
              (InnerProductSpace.rankOne Complex phi phi).toLinearMap
              (InnerProductSpace.rankOne Complex
                (n0 ⊗ₜ[Complex] c0) (n0 ⊗ₜ[Complex] c0)).toLinearMap)
            P) }
  let Psi : Semantics.Operator D →ₗ[Complex]
      Semantics.Operator (Semantics.CompositeSystem
        (Semantics.CompositeSystem (Semantics.CompositeSystem A W) N)
          (Semantics.CompositeSystem X D)) :=
    { toFun := fun P =>
        TensorProduct.map
          (InnerProductSpace.rankOne Complex
            (phi ⊗ₜ[Complex] n0) (phi ⊗ₜ[Complex] n0)).toLinearMap
          (TensorProduct.map (InnerProductSpace.rankOne Complex c0 c0).toLinearMap P)
      map_add' := by
        intro P Q
        rw [TensorProduct.map_add_right, TensorProduct.map_add_right]
      map_smul' := by
        intro a P
        calc
          TensorProduct.map
              (InnerProductSpace.rankOne Complex
                (phi ⊗ₜ[Complex] n0) (phi ⊗ₜ[Complex] n0)).toLinearMap
              (TensorProduct.map
                (InnerProductSpace.rankOne Complex c0 c0).toLinearMap (a • P)) =
            TensorProduct.map
              (InnerProductSpace.rankOne Complex
                (phi ⊗ₜ[Complex] n0) (phi ⊗ₜ[Complex] n0)).toLinearMap
              (a • TensorProduct.map
                (InnerProductSpace.rankOne Complex c0 c0).toLinearMap P) := by
                  rw [TensorProduct.map_smul_right]
          _ = a • TensorProduct.map
              (InnerProductSpace.rankOne Complex
                (phi ⊗ₜ[Complex] n0) (phi ⊗ₜ[Complex] n0)).toLinearMap
              (TensorProduct.map
                (InnerProductSpace.rankOne Complex c0 c0).toLinearMap P) := by
                  exact TensorProduct.map_smul_right _ _ _ }
  have hPhiPsi : Phi = Psi := by
    apply Semantics.QuditSubsystem.linearMap_ext_of_rankOne_basis
      (stdOrthonormalBasis Complex D) Phi Psi
    intro d d'
    dsimp [Phi, Psi]
    rw [Semantics.DensityOperator.tensorMap_rankOne]
    rw [Semantics.DensityOperator.tensorMap_rankOne]
    rw [Semantics.QuditSubsystem.conjOperator_rankOne]
    simp only [productBlockRegrouping_apply_tmul_tmul]
    rw [Semantics.DensityOperator.tensorMap_rankOne]
    rw [Semantics.DensityOperator.tensorMap_rankOne]
  exact congrArg (fun F => F P_D) hPhiPsi
end QEC.Bounds.BPTCommutingProjectorModel
