-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.xzSupport_mul_xzSupport_normal_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:28:12.868082+00:00
-- url     : https://prove2.me/submissions/20e38256-a72e-4c7a-82ac-f126e41fbad7

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_localXSupport_phase
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
theorem _root_.solution
    (x1 z1 x2 z2 : Word (ZMod 2) ι) :
    ((Semantics.Qubit.localXSupport (binarySupport x1) *
          Semantics.Qubit.localZSupport (binarySupport z1)) *
        (Semantics.Qubit.localXSupport (binarySupport x2) *
          Semantics.Qubit.localZSupport (binarySupport z2))) =
      binarySwapPhase x2 z1 •
        ((Semantics.Qubit.localXSupport (binarySupport x1) *
            Semantics.Qubit.localXSupport (binarySupport x2)) *
          (Semantics.Qubit.localZSupport (binarySupport z1) *
            Semantics.Qubit.localZSupport (binarySupport z2))) := by
  calc
    ((Semantics.Qubit.localXSupport (binarySupport x1) *
          Semantics.Qubit.localZSupport (binarySupport z1)) *
        (Semantics.Qubit.localXSupport (binarySupport x2) *
          Semantics.Qubit.localZSupport (binarySupport z2)))
        = Semantics.Qubit.localXSupport (binarySupport x1) *
            (Semantics.Qubit.localZSupport (binarySupport z1) *
              Semantics.Qubit.localXSupport (binarySupport x2)) *
              Semantics.Qubit.localZSupport (binarySupport z2) := by
          simp [mul_assoc]
    _ = Semantics.Qubit.localXSupport (binarySupport x1) *
          (binarySwapPhase x2 z1 •
            (Semantics.Qubit.localXSupport (binarySupport x2) *
              Semantics.Qubit.localZSupport (binarySupport z1))) *
            Semantics.Qubit.localZSupport (binarySupport z2) := by
          rw [show
            Semantics.Qubit.localZSupport (binarySupport z1) *
                Semantics.Qubit.localXSupport (binarySupport x2) =
              binarySwapPhase x2 z1 •
                (Semantics.Qubit.localXSupport (binarySupport x2) *
                  Semantics.Qubit.localZSupport (binarySupport z1)) from by
            simpa [binarySwapPhase] using
              (Semantics.Qubit.localZSupport_localXSupport_phase
                (xSupport := binarySupport x2) (zSupport := binarySupport z1))]
    _ = binarySwapPhase x2 z1 •
        ((Semantics.Qubit.localXSupport (binarySupport x1) *
            Semantics.Qubit.localXSupport (binarySupport x2)) *
          (Semantics.Qubit.localZSupport (binarySupport z1) *
            Semantics.Qubit.localZSupport (binarySupport z2))) := by
          simp [mul_assoc]
end QEC.Coding.PauliSymplectic
