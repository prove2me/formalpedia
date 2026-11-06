-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.toQubitOperator_mul_normal_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:29:45.391564+00:00
-- url     : https://prove2.me/submissions/df24cc12-9ce6-470d-aed4-1ce22ec82d5e

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_xzSupport_mul_xzSupport_normal_order
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_mul_expand
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
    toQubitOperator P * toQubitOperator Q =
      (binaryPhaseScalar P.phase * binaryPhaseScalar Q.phase *
          binarySwapPhase Q.vector.xPart P.vector.zPart) •
        ((Semantics.Qubit.localXSupport (xSupport P) *
            Semantics.Qubit.localXSupport (xSupport Q)) *
          (Semantics.Qubit.localZSupport (zSupport P) *
            Semantics.Qubit.localZSupport (zSupport Q))) := by
  calc
    toQubitOperator P * toQubitOperator Q =
        (binaryPhaseScalar P.phase * binaryPhaseScalar Q.phase) •
          ((Semantics.Qubit.localXSupport (xSupport P) *
              Semantics.Qubit.localZSupport (zSupport P)) *
            (Semantics.Qubit.localXSupport (xSupport Q) *
              Semantics.Qubit.localZSupport (zSupport Q))) :=
      toQubitOperator_mul_expand P Q
    _ = (binaryPhaseScalar P.phase * binaryPhaseScalar Q.phase) •
          (binarySwapPhase Q.vector.xPart P.vector.zPart •
            ((Semantics.Qubit.localXSupport (xSupport P) *
                Semantics.Qubit.localXSupport (xSupport Q)) *
              (Semantics.Qubit.localZSupport (zSupport P) *
                Semantics.Qubit.localZSupport (zSupport Q)))) := by
      rw [show
        ((Semantics.Qubit.localXSupport (xSupport P) *
              Semantics.Qubit.localZSupport (zSupport P)) *
            (Semantics.Qubit.localXSupport (xSupport Q) *
              Semantics.Qubit.localZSupport (zSupport Q))) =
          binarySwapPhase Q.vector.xPart P.vector.zPart •
            ((Semantics.Qubit.localXSupport (xSupport P) *
                Semantics.Qubit.localXSupport (xSupport Q)) *
              (Semantics.Qubit.localZSupport (zSupport P) *
                Semantics.Qubit.localZSupport (zSupport Q))) from by
        simpa [xSupport, zSupport] using
          (xzSupport_mul_xzSupport_normal_order
            (x1 := P.vector.xPart) (z1 := P.vector.zPart)
            (x2 := Q.vector.xPart) (z2 := Q.vector.zPart))]
    _ = (binaryPhaseScalar P.phase * binaryPhaseScalar Q.phase *
          binarySwapPhase Q.vector.xPart P.vector.zPart) •
        ((Semantics.Qubit.localXSupport (xSupport P) *
            Semantics.Qubit.localXSupport (xSupport Q)) *
          (Semantics.Qubit.localZSupport (zSupport P) *
            Semantics.Qubit.localZSupport (zSupport Q))) := by
      simp [smul_smul, mul_assoc]
end QEC.Coding.PauliSymplectic
