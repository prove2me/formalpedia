-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_inducedMap_rankOne_tmul_eq_replacement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:34:42.580026+00:00
-- url     : https://prove2.me/submissions/9f187531-a286-46b3-bd2a-b3384414d84e

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_inducedMap_rankOne_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureChannel_rankOne_tmul
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_prepareFactorized_apply_rankOne
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution
    (S : QuditSubsystem q) (rho : DensityOperator S.selectedSystem)
    (a b : Fin (Module.finrank Complex S.selectedSystem))
    (k l : S.complementSystem) :
    (S.replacementFactorizedKraus rho).inducedMap
      (InnerProductSpace.rankOne Complex
        (((stdOrthonormalBasis Complex S.selectedSystem) a) ⊗ₜ[Complex] k)
        (((stdOrthonormalBasis Complex S.selectedSystem) b) ⊗ₜ[Complex] l)).toLinearMap =
      S.prepareFactorized rho
        (S.erasureChannel
          (InnerProductSpace.rankOne Complex
            (((stdOrthonormalBasis Complex S.selectedSystem) a) ⊗ₜ[Complex] k)
            (((stdOrthonormalBasis Complex S.selectedSystem) b) ⊗ₜ[Complex] l)).toLinearMap) := by
  by_cases hab : a = b
  · subst b
    rw [S.replacementFactorizedKraus_inducedMap_rankOne_tmul]
    rw [S.erasureChannel_rankOne_tmul]
    simp
    exact (S.prepareFactorized_apply_rankOne rho k l).symm
  · rw [S.replacementFactorizedKraus_inducedMap_rankOne_tmul]
    simp only [if_neg hab]
    rw [S.erasureChannel_rankOne_tmul]
    rw [(stdOrthonormalBasis Complex S.selectedSystem).orthonormal.inner_eq_zero (Ne.symm hab)]
    simp
end QEC.Semantics.QuditSubsystem
