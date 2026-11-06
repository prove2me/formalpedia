-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.prepareFactorized_pureDensity_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:59:51.863109+00:00
-- url     : https://prove2.me/submissions/7e9ec254-f352-4924-aab5-a12543210127

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceReordering_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorizationWithReference_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceTransport_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_tensorMap_sum_right_reference
import Theorems.Thm_QEC_Semantics_QuditSubsystem_tensorMap_sum_left_reference
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_operator_eq_sum_rankOne_basis
import Theorems.Thm_QEC_Semantics_QuditSubsystem_prepareFactorized_apply_rankOne
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
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
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceReordering_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.registerFactorizationWithReference_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceTransport_apply_tmul

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S : QuditSubsystem q)
    (u : S.selectedSystem) (hu : ‖u‖ ^ 2 = 1) (A : Operator S.complementSystem) :
    S.prepareFactorized (pureDensity u hu) A =
      TensorProduct.map (InnerProductSpace.rankOne Complex u u).toLinearMap A := by
  let b := stdOrthonormalBasis Complex S.complementSystem
  rw [operator_eq_sum_rankOne_basis S.complementSystem b A]
  simp only [map_sum]
  rw [tensorMap_sum_right_reference]
  apply Finset.sum_congr rfl
  intro i _
  rw [S.prepareFactorized_apply_rankOne]
  calc
    (∑ k, (InnerProductSpace.rankOne Complex
      (S.densityEnsembleVectors (pureDensity u hu) k ⊗ₜ[Complex] (A (b i)))
      (S.densityEnsembleVectors (pureDensity u hu) k ⊗ₜ[Complex] (b i))).toLinearMap) =
        ∑ k, TensorProduct.map
          (InnerProductSpace.rankOne Complex
            (S.densityEnsembleVectors (pureDensity u hu) k)
            (S.densityEnsembleVectors (pureDensity u hu) k)).toLinearMap
          (InnerProductSpace.rankOne Complex (A (b i)) (b i)).toLinearMap := by
            apply Finset.sum_congr rfl
            intro k _
            rw [tensorMap_rankOne]
    _ = TensorProduct.map (∑ k,
        (InnerProductSpace.rankOne Complex
          (S.densityEnsembleVectors (pureDensity u hu) k)
          (S.densityEnsembleVectors (pureDensity u hu) k)).toLinearMap)
        (InnerProductSpace.rankOne Complex (A (b i)) (b i)).toLinearMap := by
          rw [tensorMap_sum_left_reference]
    _ = TensorProduct.map (pureDensity u hu).toOperator
        (InnerProductSpace.rankOne Complex (A (b i)) (b i)).toLinearMap := by
          rw [← S.densityEnsemble_specification]
    _ = TensorProduct.map (InnerProductSpace.rankOne Complex u u).toLinearMap
        (InnerProductSpace.rankOne Complex (A (b i)) (b i)).toLinearMap := by
          rw [pureDensity_toOperator]
end QEC.Semantics.QuditSubsystem
