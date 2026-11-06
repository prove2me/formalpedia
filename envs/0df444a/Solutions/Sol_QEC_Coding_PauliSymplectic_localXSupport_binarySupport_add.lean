-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.localXSupport_binarySupport_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:24:09.376276+00:00
-- url     : https://prove2.me/submissions/225794e9-ffcd-4b53-9f68-72c76257dc53

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution (x y : Word (ZMod 2) ι) :
    Semantics.Qubit.localXSupport (binarySupport (x + y)) =
      Semantics.Qubit.localXSupport (binarySupport x) *
        Semantics.Qubit.localXSupport (binarySupport y) := by
  ext ψ bits
  simp [Module.End.mul_apply]
  apply congrArg (fun bits' => ψ bits')
  funext i
  by_cases hxi : x i = 0
  · by_cases hyi : y i = 0
    · simp [Semantics.Qubit.flipSupport, binarySupport, hxi, hyi]
    · have hyi1 : y i = 1 := zmod_two_eq_one_of_ne_zero hyi
      simp [Semantics.Qubit.flipSupport, binarySupport, hxi, hyi1]
  · have hxi1 : x i = 1 := zmod_two_eq_one_of_ne_zero hxi
    by_cases hyi : y i = 0
    · simp [Semantics.Qubit.flipSupport, binarySupport, hxi1, hyi]
    · have hyi1 : y i = 1 := zmod_two_eq_one_of_ne_zero hyi
      have hsum : (1 : ZMod 2) + 1 = 0 := by decide
      simp [Semantics.Qubit.flipSupport, binarySupport, hxi1, hyi1, hsum]
end QEC.Coding.PauliSymplectic
