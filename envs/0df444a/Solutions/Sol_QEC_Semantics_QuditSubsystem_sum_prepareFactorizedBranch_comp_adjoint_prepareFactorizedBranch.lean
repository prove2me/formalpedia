-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.sum_prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:32:49.870923+00:00
-- url     : https://prove2.me/submissions/567ca013-82a6-400e-87e5-5e2efdf0b5f9

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocal_sum
import Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocal_one
import Theorems.Thm_QEC_Semantics_QuditSubsystem_prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
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
    (S : QuditSubsystem q) {κ : Type v} [Fintype κ]
    (b : OrthonormalBasis κ Complex S.selectedSystem) :
    ∑ a : κ, (S.prepareFactorizedBranch (b a)).comp
      (LinearMap.adjoint (S.prepareFactorizedBranch (b a))) = 1 := by
  calc
    ∑ a : κ, (S.prepareFactorizedBranch (b a)).comp
        (LinearMap.adjoint (S.prepareFactorizedBranch (b a))) =
        ∑ a : κ, S.extendLocal
          (InnerProductSpace.rankOne Complex (b a) (b a)).toLinearMap := by
            apply Finset.sum_congr rfl
            intro a _
            exact S.prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch (b a) (b a)
    _ = S.extendLocal (∑ a : κ,
        (InnerProductSpace.rankOne Complex (b a) (b a)).toLinearMap) := by
          symm
          simpa using S.extendLocal_sum (Finset.univ : Finset κ)
            (fun a => (InnerProductSpace.rankOne Complex (b a) (b a)).toLinearMap)
    _ = S.extendLocal 1 := by
          congr 1
          change (∑ a : κ,
            (InnerProductSpace.rankOne Complex (b a) (b a)).toLinearMap) = LinearMap.id
          simpa using congrArg ContinuousLinearMap.toLinearMap
            (OrthonormalBasis.sum_rankOne_eq_id b)
    _ = 1 := S.extendLocal_one
end QEC.Semantics.QuditSubsystem
