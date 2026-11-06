-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.erasureRecovery_allSelected_detectableOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:08:10.691194+00:00
-- url     : https://prove2.me/submissions/9bd82147-aec3-497a-accd-34611c579526

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureRecovery_rankOne_detectableOnWithScalar
import Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocalToRegister_smul_reference
import Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocalToRegister_sum_reference
import Theorems.Thm_QEC_Semantics_QuditSubsystem_operator_eq_sum_rankOne_matrix_basis_reference
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
    (C : QuantumCode (Qudit.QuditRegister q))
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q))
    (hcorrect : Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister recovery)
    (A : Operator S.selectedSystem) :
    DetectableOn C (S.extendLocalToRegister A) := by
  classical
  let b := stdOrthonormalBasis Complex S.selectedSystem
  choose scalar hscalar using fun i j =>
    S.erasureRecovery_rankOne_detectableOnWithScalar C recovery hcorrect i j
  rw [operator_eq_sum_rankOne_matrix_basis_reference b A]
  rw [S.extendLocalToRegister_sum_reference Finset.univ]
  simp_rw [S.extendLocalToRegister_sum_reference]
  simp_rw [S.extendLocalToRegister_smul_reference]
  refine ⟨∑ i, ∑ j, inner Complex (b j) (A (b i)) * scalar j i, ?_⟩
  intro x hx y hy
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, inner_sum, inner_smul_right]
  calc
    (∑ x_1, ∑ x_2,
        inner Complex (b x_2) (A (b x_1)) *
          inner Complex x
            (S.extendLocalToRegister
              ((InnerProductSpace.rankOne Complex (b x_2) (b x_1)).toLinearMap) y)) =
        ∑ i, ∑ j, inner Complex (b j) (A (b i)) *
          (scalar j i * inner Complex x y) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            rw [hscalar j i x hx y hy]
    _ = (∑ i, ∑ j, inner Complex (b j) (A (b i)) * scalar j i) *
        inner Complex x y := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
end QEC.Semantics.QuditSubsystem
