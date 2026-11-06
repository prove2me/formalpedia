-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.matrixElement_zero_of_syndromeSeparatedByCheckSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:36:28.994985+00:00
-- url     : https://prove2.me/submissions/4e332cd9-28aa-4075-894d-17b3a52d59ce

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_binaryMul
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_binaryDagger
import Theorems.Thm_QEC_Coding_PauliSymplectic_inner_toQubitOperator_eq_zero_of_checkDistinguishes
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
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {E F : Binary ι}
    (hsep : syndromeSeparatedByCheckSet (binaryCSSCheckSet xCode zCode) E F)
    {ψ φ : Semantics.Qubit.QubitRegister ι}
    (hψ : ψ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier)
    (hφ : φ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier) :
    inner Complex (toQubitOperator E ψ) (toQubitOperator F φ) = 0 := by
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
  have hrelZero : inner Complex (toQubitOperator R φ) ψ = 0 := by
    exact inner_toQubitOperator_eq_zero_of_checkDistinguishes xCode zCode hdual
      (P := R) (by simpa [R, syndromeSeparatedByCheckSet] using hsep) hφ hψ
  have hflipZero : inner Complex ψ (toQubitOperator R φ) = 0 := by
    have hconj := congrArg star hrelZero
    simpa [inner_conj_symm] using hconj
  simpa [hrelInner] using hflipZero
end QEC.Coding.PauliSymplectic
