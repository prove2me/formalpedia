-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.inner_toQubitOperator_eq_zero_of_checkDistinguishes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:34:02.897192+00:00
-- url     : https://prove2.me/submissions/d478c366-fc6f-441a-a277-3214bc6be3fc

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_anticommute_of_not_commutes
import Theorems.Thm_QEC_Coding_PauliSymplectic_adjoint_toQubitOperator_eq_self_of_mem_binaryCSSCheckSet
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
    {P : Binary ι}
    (hsep : checkDistinguishes (binaryCSSCheckSet xCode zCode) P)
    {ψ φ : Semantics.Qubit.QubitRegister ι}
    (hψ : ψ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier)
    (hφ : φ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier) :
    inner Complex (toQubitOperator P ψ) φ = 0 := by
  rcases hsep with ⟨S, hS, hnotCommutes⟩
  let A := toQubitOperator S
  let B := toQubitOperator P
  have hAadj : LinearMap.adjoint A = A := by
    simpa [A] using adjoint_toQubitOperator_eq_self_of_mem_binaryCSSCheckSet xCode zCode hS
  have hψS : A ψ = ψ := by
    simpa [A] using
      (mem_binaryCSSQuantumCodeOfDualLe_carrier xCode zCode hdual ψ).1 hψ S hS
  have hφS : A φ = φ := by
    simpa [A] using
      (mem_binaryCSSQuantumCodeOfDualLe_carrier xCode zCode hdual φ).1 hφ S hS
  have hanti : B * A = -(A * B) := by
    simpa [A, B] using toQubitOperator_anticommute_of_not_commutes P S hnotCommutes
  have hanti' : A * B = -(B * A) := by
    rw [hanti]
    simp
  have hABψ : A (B ψ) = -B ψ := by
    have happ := congrArg
      (fun T : Semantics.Operator (Semantics.Qubit.QubitRegister ι) => T ψ) hanti'
    simpa [Module.End.mul_apply, hψS] using happ
  let a : Complex := inner Complex (B ψ) φ
  have ha_neg : a = -a := by
    calc
      a = inner Complex (B ψ) (A φ) := by
          simp [a, hφS]
      _ = inner Complex (LinearMap.adjoint A (B ψ)) φ := by
          simpa using (LinearMap.adjoint_inner_left (𝕜 := Complex) A φ (B ψ)).symm
      _ = inner Complex (A (B ψ)) φ := by
          rw [hAadj]
      _ = inner Complex (-B ψ) φ := by
          rw [hABψ]
      _ = -a := by
          simp [a]
  have hadd : a + a = 0 := eq_neg_iff_add_eq_zero.mp ha_neg
  have htwo : (2 : Complex) * a = 0 := by
    simpa [two_mul] using hadd
  have hzero : a = 0 := (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  simpa [a, B] using hzero
end QEC.Coding.PauliSymplectic
