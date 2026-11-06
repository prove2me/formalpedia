-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.toQubitOperator_commute_of_binarySwapPhase_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:31:39.609527+00:00
-- url     : https://prove2.me/submissions/4190d030-9d38-4646-9e7b-7494e6c4a43a

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_commute
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_commute
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_mul_normal_order
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
theorem _root_.solution (P Q : Binary ι)
    (hphase :
      binarySwapPhase Q.vector.xPart P.vector.zPart =
        binarySwapPhase P.vector.xPart Q.vector.zPart) :
    toQubitOperator P * toQubitOperator Q = toQubitOperator Q * toQubitOperator P := by
  let XP := Semantics.Qubit.localXSupport (xSupport P)
  let XQ := Semantics.Qubit.localXSupport (xSupport Q)
  let ZP := Semantics.Qubit.localZSupport (zSupport P)
  let ZQ := Semantics.Qubit.localZSupport (zSupport Q)
  have hxcomm : XP * XQ = XQ * XP := by
    simpa [XP, XQ] using Semantics.Qubit.localXSupport_commute (xSupport P) (xSupport Q)
  have hzcomm : ZP * ZQ = ZQ * ZP := by
    simpa [ZP, ZQ] using Semantics.Qubit.localZSupport_commute (zSupport P) (zSupport Q)
  have hscalar :
      binaryPhaseScalar P.phase * binaryPhaseScalar Q.phase *
          binarySwapPhase P.vector.xPart Q.vector.zPart =
        binaryPhaseScalar Q.phase * binaryPhaseScalar P.phase *
          binarySwapPhase P.vector.xPart Q.vector.zPart := by
    ring
  calc
    toQubitOperator P * toQubitOperator Q =
        (binaryPhaseScalar P.phase * binaryPhaseScalar Q.phase *
            binarySwapPhase Q.vector.xPart P.vector.zPart) •
          ((XP * XQ) * (ZP * ZQ)) := by
            simpa [XP, XQ, ZP, ZQ] using toQubitOperator_mul_normal_order P Q
    _ = (binaryPhaseScalar P.phase * binaryPhaseScalar Q.phase *
            binarySwapPhase P.vector.xPart Q.vector.zPart) •
          ((XP * XQ) * (ZP * ZQ)) := by
            rw [hphase]
    _ = (binaryPhaseScalar Q.phase * binaryPhaseScalar P.phase *
            binarySwapPhase P.vector.xPart Q.vector.zPart) •
          ((XQ * XP) * (ZQ * ZP)) := by
            rw [hscalar, hxcomm, hzcomm]
    _ = toQubitOperator Q * toQubitOperator P := by
            simpa [XP, XQ, ZP, ZQ] using (toQubitOperator_mul_normal_order Q P).symm
end QEC.Coding.PauliSymplectic
