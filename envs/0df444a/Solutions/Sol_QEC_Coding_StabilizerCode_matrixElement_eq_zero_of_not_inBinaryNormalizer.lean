-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.matrixElement_eq_zero_of_not_inBinaryNormalizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:41:52.05846+00:00
-- url     : https://prove2.me/submissions/cdff056e-5609-46d2-b2e1-c41f3ed89fc9

import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Symplectic
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_Stabilizer_Detectability
import Theorems.Thm_QEC_Coding_StabilizerCode_not_inBinaryNormalizer_iff_exists_not_commutes
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_adjoint_toQubitOperator_eq_binaryDagger
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_anticommute_of_not_commutes
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
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
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
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
universe u
open QEC.Coding.StabilizerCode
open PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Coding.StabilizerCode
theorem _root_.solution
    (Q : SourceValidBinary ι) (E : Binary ι)
    (hE : ¬ Q.1.InBinaryNormalizer E) :
    ∀ ψ, ψ ∈ Q.1.code.carrier →
      ∀ φ, φ ∈ Q.1.code.carrier →
        inner Complex ψ (toQubitOperator E φ) = 0 := by
  rcases (not_inBinaryNormalizer_iff_exists_not_commutes Q.1 E).1 hE with
    ⟨S, hS, hNotCommutes⟩
  have hSdagger : binaryDagger S ∈ Q.1.generatedGroup :=
    binaryDagger_mem_generatedGroup Q.1 hS
  intro ψ hψ φ hφ
  have hSfixPhi : toQubitOperator S φ = φ :=
    ((Q.2.2 φ).1 hφ) S hS
  have hSdaggerFixPsi : toQubitOperator (binaryDagger S) ψ = ψ :=
    ((Q.2.2 ψ).1 hψ) (binaryDagger S) hSdagger
  let A := toQubitOperator S
  let B := toQubitOperator E
  have hAdjointFixPsi : LinearMap.adjoint A ψ = ψ := by
    change LinearMap.adjoint (toQubitOperator S) ψ = ψ
    rw [adjoint_toQubitOperator_eq_binaryDagger]
    exact hSdaggerFixPsi
  have hAnticommutes : B * A = -(A * B) := by
    simpa [A, B] using
      toQubitOperator_anticommute_of_not_commutes E S hNotCommutes
  have hErrorAction : B φ = -A (B φ) := by
    have hApply := congrArg
      (fun T : Semantics.Operator (Semantics.Qubit.QubitRegister ι) => T φ)
      hAnticommutes
    simpa [A, Module.End.mul_apply, hSfixPhi] using hApply
  let a : Complex := inner Complex ψ (B φ)
  have haNeg : a = -a := by
    calc
      a = inner Complex ψ (-A (B φ)) := by
        exact congrArg (fun v => inner Complex ψ v) hErrorAction
      _ = -inner Complex ψ (A (B φ)) := by simp
      _ = -inner Complex (LinearMap.adjoint A ψ) (B φ) := by
        rw [← LinearMap.adjoint_inner_left]
      _ = -a := by rw [hAdjointFixPsi]
  have hAdd : a + a = 0 := eq_neg_iff_add_eq_zero.mp haNeg
  have hTwo : (2 : Complex) * a = 0 := by
    simpa [two_mul] using hAdd
  have haZero : a = 0 := (mul_eq_zero.mp hTwo).resolve_left (by norm_num)
  simpa [a, B] using haZero
end QEC.Coding.StabilizerCode
