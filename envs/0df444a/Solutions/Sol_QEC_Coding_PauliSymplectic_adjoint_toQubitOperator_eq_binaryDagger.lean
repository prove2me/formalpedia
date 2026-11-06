-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.adjoint_toQubitOperator_eq_binaryDagger
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:30:15.545338+00:00
-- url     : https://prove2.me/submissions/68207a66-7f13-4f5c-b057-c2b7ce9170de

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_localXSupport_phase
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_adjoint
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_adjoint
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPhaseScalar_binaryDaggerPhase
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
theorem _root_.solution (P : Binary ι) :
    LinearMap.adjoint (toQubitOperator P) = toQubitOperator (binaryDagger P) := by
  let X := Semantics.Qubit.localXSupport (xSupport P)
  let Z := Semantics.Qubit.localZSupport (zSupport P)
  have hAdjXZ : LinearMap.adjoint (X * Z) = Z * X := by
    simp [X, Z, Module.End.mul_eq_comp, Semantics.Qubit.localXSupport_adjoint,
      Semantics.Qubit.localZSupport_adjoint]
  calc
    LinearMap.adjoint (toQubitOperator P) =
        binaryPhaseScalar P.phase •
          (Semantics.Qubit.localZSupport (zSupport P) *
            Semantics.Qubit.localXSupport (xSupport P)) := by
          calc
            LinearMap.adjoint (toQubitOperator P)
                = star (binaryPhaseScalar P.phase) • LinearMap.adjoint (X * Z) := by
                    change
                      LinearMap.adjoint (binaryPhaseScalar P.phase • (X * Z)) =
                        star (binaryPhaseScalar P.phase) • LinearMap.adjoint (X * Z)
                    exact
                      map_smulₛₗ
                        (LinearMap.adjoint :
                          (Semantics.Operator (Semantics.Qubit.QubitRegister ι)) ≃ₗ⋆[Complex]
                            Semantics.Operator (Semantics.Qubit.QubitRegister ι))
                        (binaryPhaseScalar P.phase) (X * Z)
            _ = binaryPhaseScalar P.phase •
                (Semantics.Qubit.localZSupport (zSupport P) *
                  Semantics.Qubit.localXSupport (xSupport P)) := by
                    simp [hAdjXZ, X, Z]
    _ = binaryPhaseScalar P.phase •
        (binarySwapPhase P.vector.xPart P.vector.zPart •
          (Semantics.Qubit.localXSupport (xSupport P) *
            Semantics.Qubit.localZSupport (zSupport P))) := by
          rw [show
            Semantics.Qubit.localZSupport (zSupport P) *
                Semantics.Qubit.localXSupport (xSupport P) =
              binarySwapPhase P.vector.xPart P.vector.zPart •
                (Semantics.Qubit.localXSupport (xSupport P) *
                  Semantics.Qubit.localZSupport (zSupport P)) from by
            simpa [binarySwapPhase, xSupport, zSupport] using
              (Semantics.Qubit.localZSupport_localXSupport_phase
                (xSupport := binarySupport P.vector.xPart)
                (zSupport := binarySupport P.vector.zPart))]
    _ = toQubitOperator (binaryDagger P) := by
          simp [toQubitOperator, binaryDagger, xSupport, zSupport,
            binaryPhaseScalar_binaryDaggerPhase, smul_smul]
end QEC.Coding.PauliSymplectic
