-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.extendLocalToRegister_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:23:21.517853+00:00
-- url     : https://prove2.me/submissions/cfe8bf56-fb0c-4028-933f-8ef25bbe00d5

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocalToRegister_add
import Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocalToRegister_zero
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
theorem _root_.solution (S : QuditSubsystem q) {κ : Type v}
    (s : Finset κ) (f : κ → Operator S.selectedSystem) :
    S.extendLocalToRegister (∑ i ∈ s, f i) = ∑ i ∈ s, S.extendLocalToRegister (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [S.extendLocalToRegister_zero]
  | insert i s his ih =>
      calc
        S.extendLocalToRegister (∑ j ∈ insert i s, f j) =
            S.extendLocalToRegister (f i + ∑ j ∈ s, f j) := by
              rw [Finset.sum_insert his]
        _ = S.extendLocalToRegister (f i) +
            S.extendLocalToRegister (∑ j ∈ s, f j) :=
              S.extendLocalToRegister_add (f i) (∑ j ∈ s, f j)
        _ = S.extendLocalToRegister (f i) + ∑ j ∈ s,
            S.extendLocalToRegister (f j) := by rw [ih]
        _ = ∑ j ∈ insert i s, S.extendLocalToRegister (f j) := by
              rw [Finset.sum_insert his]
end QEC.Semantics.QuditSubsystem
