-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.matrixElement_eq_phase_mul_inner_of_relative_vector_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:34:06.88295+00:00
-- url     : https://prove2.me/submissions/af7b733e-dda2-4e08-886f-2ccfda6ba0e9

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_eq_phase_smul_id_of_vector_eq_zero
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_binaryMul
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_binaryDagger
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
    {E F : Binary ι}
    (hx : (binaryMul (binaryDagger E) F).vector.xPart = 0)
    (hz : (binaryMul (binaryDagger E) F).vector.zPart = 0)
    {ψ φ : Semantics.Qubit.QubitRegister ι} :
    inner Complex (toQubitOperator E ψ) (toQubitOperator F φ) =
      binaryPhaseScalar (binaryMul (binaryDagger E) F).phase * inner Complex ψ φ := by
  let R := binaryMul (binaryDagger E) F
  have hrelInner :
      inner Complex (toQubitOperator E ψ) (toQubitOperator F φ) =
        inner Complex ψ (toQubitOperator R φ) := by
    calc
      inner Complex (toQubitOperator E ψ) (toQubitOperator F φ) =
          inner Complex ψ (LinearMap.adjoint (toQubitOperator E) (toQubitOperator F φ)) := by
            simpa using
              (LinearMap.adjoint_inner_right (𝕜 := Complex) (toQubitOperator E) ψ
                (toQubitOperator F φ)).symm
      _ = inner Complex ψ (toQubitOperator (binaryDagger E) (toQubitOperator F φ)) := by
            rw [← toQubitOperator_binaryDagger E]
      _ = inner Complex ψ ((toQubitOperator (binaryDagger E) * toQubitOperator F) φ) := by
            simp [Module.End.mul_apply]
      _ = inner Complex ψ (toQubitOperator R φ) := by
            rw [← toQubitOperator_binaryMul (binaryDagger E) F]
  have hphase :
      toQubitOperator R =
        binaryPhaseScalar R.phase •
          (1 : Semantics.Operator (Semantics.Qubit.QubitRegister ι)) :=
    toQubitOperator_eq_phase_smul_id_of_vector_eq_zero
      (P := R) (by simpa [R] using hx) (by simpa [R] using hz)
  calc
    inner Complex (toQubitOperator E ψ) (toQubitOperator F φ) =
        inner Complex ψ (toQubitOperator R φ) := hrelInner
    _ = inner Complex ψ
        ((binaryPhaseScalar R.phase •
          (1 : Semantics.Operator (Semantics.Qubit.QubitRegister ι))) φ) := by
          rw [hphase]
    _ = binaryPhaseScalar R.phase * inner Complex ψ φ := by
          simp
end QEC.Coding.PauliSymplectic
