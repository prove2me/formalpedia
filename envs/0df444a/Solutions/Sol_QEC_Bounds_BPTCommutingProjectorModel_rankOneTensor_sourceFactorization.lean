-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.rankOneTensor_sourceFactorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:35:51.54018+00:00
-- url     : https://prove2.me/submissions/a4ff2392-8e79-418d-ace0-9331cf0a586c

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_rankOne_sandwich
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingLeft_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingRight_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_productBlockRegrouping_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_productBlockRegrouping_apply_tmul_tmul
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
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingLeft_apply_tmul
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingRight_apply_tmul
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.mem_regionSubsystem_selected_iff
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.productBlockRegrouping_apply_tmul
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.productBlockRegrouping_apply_tmul_tmul
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
open QEC.Bounds.BPTCommutingProjectorModel
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (phi : H) (hphi : ‖phi‖ = 1) (Q : Semantics.Operator K)
    (A : Semantics.Operator H) (B : Semantics.Operator K) :
    let rankOne := (InnerProductSpace.rankOne Complex phi phi).toLinearMap
    let codeProjector := TensorProduct.map rankOne Q
    codeProjector * TensorProduct.map A (1 : Semantics.Operator K) *
        TensorProduct.map (1 : Semantics.Operator H) B * codeProjector =
      (inner Complex phi (A phi)) •
        (codeProjector * TensorProduct.map (1 : Semantics.Operator H) B *
          codeProjector) := by
  dsimp
  let rankOne := (InnerProductSpace.rankOne Complex phi phi).toLinearMap
  have hsandwich : rankOne * A * rankOne =
      (inner Complex phi (A phi)) • rankOne := by
    simpa [rankOne] using rankOne_sandwich phi hphi A
  have hidempotent : rankOne * rankOne = rankOne := by
    simpa [rankOne, hphi] using rankOne_sandwich phi hphi (1 : Semantics.Operator H)
  have tensorMap_mul (f₁ f₂ : Semantics.Operator H) (g₁ g₂ : Semantics.Operator K) :
      TensorProduct.map f₁ g₁ * TensorProduct.map f₂ g₂ =
        TensorProduct.map (f₁ * f₂) (g₁ * g₂) := by
    simp only [Module.End.mul_eq_comp]
    rw [← TensorProduct.map_comp]
  have hright : TensorProduct.map rankOne Q *
      TensorProduct.map (1 : Semantics.Operator H) B * TensorProduct.map rankOne Q =
      TensorProduct.map rankOne (Q * B * Q) := by
    calc
      TensorProduct.map rankOne Q * TensorProduct.map (1 : Semantics.Operator H) B *
          TensorProduct.map rankOne Q =
        TensorProduct.map (rankOne * (1 : Semantics.Operator H)) (Q * B) *
          TensorProduct.map rankOne Q := by
            rw [tensorMap_mul]
      _ = TensorProduct.map ((rankOne * (1 : Semantics.Operator H)) * rankOne)
          ((Q * B) * Q) := by
            rw [tensorMap_mul]
      _ = TensorProduct.map rankOne (Q * B * Q) := by
            simpa [hidempotent, mul_assoc]
  calc
    TensorProduct.map rankOne Q * TensorProduct.map A (1 : Semantics.Operator K) *
        TensorProduct.map (1 : Semantics.Operator H) B * TensorProduct.map rankOne Q =
      TensorProduct.map (rankOne * A) (Q * (1 : Semantics.Operator K)) *
        TensorProduct.map (1 : Semantics.Operator H) B * TensorProduct.map rankOne Q := by
          rw [tensorMap_mul]
    _ = TensorProduct.map ((rankOne * A) * (1 : Semantics.Operator H))
        ((Q * (1 : Semantics.Operator K)) * B) * TensorProduct.map rankOne Q := by
          rw [tensorMap_mul]
    _ = TensorProduct.map (((rankOne * A) * (1 : Semantics.Operator H)) * rankOne)
        (((Q * (1 : Semantics.Operator K)) * B) * Q) := by
          rw [tensorMap_mul]
    _ = TensorProduct.map (rankOne * A * rankOne) (Q * B * Q) := by
      simp [mul_assoc]
    _ = TensorProduct.map ((inner Complex phi (A phi)) • rankOne) (Q * B * Q) := by
      rw [hsandwich]
    _ = (inner Complex phi (A phi)) • TensorProduct.map rankOne (Q * B * Q) := by
      rw [TensorProduct.map_smul_left]
    _ = (inner Complex phi (A phi)) •
        (TensorProduct.map rankOne Q * TensorProduct.map (1 : Semantics.Operator H) B *
          TensorProduct.map rankOne Q) := by rw [hright]
end QEC.Bounds.BPTCommutingProjectorModel
