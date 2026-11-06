-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.erasureFactorizedKraus_inducedMap_rankOne_tmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:56:52.080739+00:00
-- url     : https://prove2.me/submissions/e18972ce-074f-4311-88ec-97cdcc8fd50e

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Theorems.Thm_QEC_Semantics_QuditSubsystem_adjoint_prepareFactorizedBranch_apply_tmul_reference
import Theorems.Thm_QEC_Semantics_QuditSubsystem_comp_rankOne_comp_adjoint_reference
import Theorems.Thm_QEC_Semantics_QuditSubsystem_sum_star_inner_mul_inner_eq_inner
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
theorem _root_.solution
    (S : QuditSubsystem q) (h h' : S.selectedSystem)
    (k k' : S.complementSystem) :
    S.erasureFactorizedKraus.inducedMap
      (InnerProductSpace.rankOne Complex (h ⊗ₜ[Complex] k)
        (h' ⊗ₜ[Complex] k')).toLinearMap =
      (inner Complex h' h) •
        (InnerProductSpace.rankOne Complex k k').toLinearMap := by
  let b := stdOrthonormalBasis Complex S.selectedSystem
  rw [FiniteKrausFamily.inducedMap_apply]
  have hterm (a : Fin (Module.finrank Complex S.selectedSystem)) :
      (S.erasureFactorizedKraus.operator a).comp
        ((InnerProductSpace.rankOne Complex (h ⊗ₜ[Complex] k)
          (h' ⊗ₜ[Complex] k')).toLinearMap.comp
          (LinearMap.adjoint (S.erasureFactorizedKraus.operator a))) =
        (InnerProductSpace.rankOne Complex
          ((inner Complex (b a) h) • k)
          ((inner Complex (b a) h') • k')).toLinearMap := by
    rw [comp_rankOne_comp_adjoint_reference]
    simp only [erasureFactorizedKraus]
    rw [S.adjoint_prepareFactorizedBranch_apply_tmul_reference,
      S.adjoint_prepareFactorizedBranch_apply_tmul_reference]
  have hsum : (∑ i, (S.erasureFactorizedKraus.operator i).comp
      ((InnerProductSpace.rankOne Complex (h ⊗ₜ[Complex] k)
        (h' ⊗ₜ[Complex] k')).toLinearMap.comp
        (LinearMap.adjoint (S.erasureFactorizedKraus.operator i))) =
      ∑ i, (InnerProductSpace.rankOne Complex
        ((inner Complex (b i) h) • k)
        ((inner Complex (b i) h') • k')).toLinearMap) := by
    apply Finset.sum_congr rfl
    intro i _
    exact hterm i
  rw [hsum]
  apply LinearMap.ext
  intro z
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  calc
    (∑ x, inner Complex ((inner Complex (b x) h') • k') z •
        ((inner Complex (b x) h) • k)) =
        (∑ x, star (inner Complex (b x) h') * inner Complex (b x) h) •
          (inner Complex k' z • k) := by
            calc
              (∑ x, inner Complex ((inner Complex (b x) h') • k') z •
                  ((inner Complex (b x) h) • k)) =
                  ∑ x, (star (inner Complex (b x) h') * inner Complex (b x) h) •
                    (inner Complex k' z • k) := by
                      apply Finset.sum_congr rfl
                      intro x _
                      rw [inner_smul_left]
                      simp only [smul_smul]
                      congr 1
                      simp only [starRingEnd_apply]
                      ring
              _ = (∑ x, star (inner Complex (b x) h') * inner Complex (b x) h) •
                  (inner Complex k' z • k) := by
                    rw [Finset.sum_smul]
    _ = (inner Complex h' h) • (inner Complex k' z • k) := by
          rw [sum_star_inner_mul_inner_eq_inner b h' h]
    _ = ((inner Complex h' h) •
        (InnerProductSpace.rankOne Complex k k').toLinearMap) z := by
          simp [InnerProductSpace.rankOne_apply, smul_smul]
end QEC.Semantics.QuditSubsystem
