-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.prepareFactorized_erasure_fixed_of_supportedOn_branch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:20:37.318196+00:00
-- url     : https://prove2.me/submissions/bc665542-32d3-4013-8129-6716257eb152

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceReordering_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorizationWithReference_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceTransport_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_prepareFactorized_pureDensity_eq_branch_sandwich
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_toOperator_adjoint_eq_self
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureChannel_prepareFactorized_apply
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
theorem _root_.solution
    (S : QuditSubsystem q) (u : S.selectedSystem) (hu : ‖u‖ ^ 2 = 1)
    (rho : DensityOperator S.factorizedSystem)
    (hsupported : ∀ z : S.factorizedSystem,
      rho.toOperator z ∈ LinearMap.range (S.prepareFactorizedBranch u)) :
    S.prepareFactorized (pureDensity u hu) (S.erasureChannel rho.toOperator) =
      rho.toOperator := by
  have huinner : inner Complex u u = 1 := by
    rw [inner_self_eq_norm_sq_to_K]
    have hcast := congrArg (fun t : ℝ => (t : Complex)) hu
    simpa using hcast
  have hisometry :
      (LinearMap.adjoint (S.prepareFactorizedBranch u)).comp
        (S.prepareFactorizedBranch u) = 1 := by
    rw [S.adjoint_prepareFactorizedBranch_comp, huinner, one_smul]
  have hleft :
      (S.prepareFactorizedBranch u).comp
        ((LinearMap.adjoint (S.prepareFactorizedBranch u)).comp rho.toOperator) =
        rho.toOperator := by
    apply LinearMap.ext
    intro z
    rcases hsupported z with ⟨k, hk⟩
    simp only [LinearMap.comp_apply]
    rw [← hk]
    have hk' := congrArg (fun T : Operator S.complementSystem => T k) hisometry
    simpa [LinearMap.comp_apply] using
      congrArg (fun v : S.complementSystem => S.prepareFactorizedBranch u v) hk'
  have hright :
      rho.toOperator.comp
        ((S.prepareFactorizedBranch u).comp
          (LinearMap.adjoint (S.prepareFactorizedBranch u))) = rho.toOperator := by
    have hadjoint := congrArg LinearMap.adjoint hleft
    simpa [LinearMap.adjoint_comp, LinearMap.comp_assoc,
      rho.toOperator_adjoint_eq_self] using hadjoint
  let compressed : Operator S.complementSystem :=
    (LinearMap.adjoint (S.prepareFactorizedBranch u)).comp
      (rho.toOperator.comp (S.prepareFactorizedBranch u))
  have hfactor :
      (S.prepareFactorizedBranch u).comp
        (compressed.comp (LinearMap.adjoint (S.prepareFactorizedBranch u))) =
        rho.toOperator := by
    change (S.prepareFactorizedBranch u).comp
        (((LinearMap.adjoint (S.prepareFactorizedBranch u)).comp
          (rho.toOperator.comp (S.prepareFactorizedBranch u))).comp
          (LinearMap.adjoint (S.prepareFactorizedBranch u))) = rho.toOperator
    calc
      (S.prepareFactorizedBranch u).comp
          (((LinearMap.adjoint (S.prepareFactorizedBranch u)).comp
            (rho.toOperator.comp (S.prepareFactorizedBranch u))).comp
            (LinearMap.adjoint (S.prepareFactorizedBranch u))) =
          ((S.prepareFactorizedBranch u).comp
            ((LinearMap.adjoint (S.prepareFactorizedBranch u)).comp rho.toOperator)).comp
            ((S.prepareFactorizedBranch u).comp
              (LinearMap.adjoint (S.prepareFactorizedBranch u))) := by
              apply LinearMap.ext
              intro z
              rfl
      _ = rho.toOperator.comp
          ((S.prepareFactorizedBranch u).comp
            (LinearMap.adjoint (S.prepareFactorizedBranch u))) := by rw [hleft]
      _ = rho.toOperator := hright
  have hprepared :
      S.prepareFactorized (pureDensity u hu) compressed = rho.toOperator := by
    rw [S.prepareFactorized_pureDensity_eq_branch_sandwich u hu]
    exact hfactor
  calc
    S.prepareFactorized (pureDensity u hu) (S.erasureChannel rho.toOperator) =
        S.prepareFactorized (pureDensity u hu)
          (S.erasureChannel
            (S.prepareFactorized (pureDensity u hu) compressed)) := by rw [hprepared]
    _ = S.prepareFactorized (pureDensity u hu) compressed := by
      rw [S.erasureChannel_prepareFactorized_apply]
    _ = rho.toOperator := hprepared
end QEC.Semantics.QuditSubsystem
