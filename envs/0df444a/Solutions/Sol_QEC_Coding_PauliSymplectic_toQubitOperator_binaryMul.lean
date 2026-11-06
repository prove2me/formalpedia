-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.toQubitOperator_binaryMul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:31:28.18174+00:00
-- url     : https://prove2.me/submissions/35deb36d-4391-4bd1-8a0b-a01ed41ffa97

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPhaseScalar_binaryMulPhase
import Theorems.Thm_QEC_Coding_PauliSymplectic_localXSupport_binarySupport_add
import Theorems.Thm_QEC_Coding_PauliSymplectic_localZSupport_binarySupport_add
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
theorem _root_.solution (P Q : Binary ι) :
    toQubitOperator (binaryMul P Q) = toQubitOperator P * toQubitOperator Q := by
  calc
    toQubitOperator (binaryMul P Q) =
        (binaryPhaseScalar P.phase * binaryPhaseScalar Q.phase *
            binarySwapPhase Q.vector.xPart P.vector.zPart) •
          ((Semantics.Qubit.localXSupport (xSupport P) *
              Semantics.Qubit.localXSupport (xSupport Q)) *
            (Semantics.Qubit.localZSupport (zSupport P) *
              Semantics.Qubit.localZSupport (zSupport Q))) := by
          simp [toQubitOperator, binaryMul, xSupport, zSupport,
            binaryPhaseScalar_binaryMulPhase, localXSupport_binarySupport_add,
            localZSupport_binarySupport_add]
    _ = toQubitOperator P * toQubitOperator Q :=
          (toQubitOperator_mul_normal_order P Q).symm
end QEC.Coding.PauliSymplectic
