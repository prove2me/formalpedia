-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.inGeneratedGroupUpToSign_iff_exists_nonzero_detectableOnWithScalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:57:30.578678+00:00
-- url     : https://prove2.me/submissions/f90ab77b-9c34-4f6b-9ac7-1c20a5cfd2fa

import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_Degeneracy
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_StabilizerCode_detectableOn_toQubitOperator_iff_inGeneratedGroupUpToSign_or_not_inBinaryNormalizer
import Theorems.Thm_QEC_Coding_StabilizerCode_exists_nonzero_mem_code
import Theorems.Thm_QEC_Coding_StabilizerCode_matrixElement_eq_zero_of_not_inBinaryNormalizer
import Theorems.Thm_QEC_Coding_StabilizerCode_scalar_action_on_code_of_inGeneratedGroupUpToSign
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
open QEC.Coding.StabilizerCode
universe u
open PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Coding.StabilizerCode
theorem _root_.solution
    (Q : SourceValidBinary ι) (E : Binary ι) :
    Q.1.InGeneratedGroupUpToSign E ↔
      ∃ c : Complex, c ≠ 0 ∧
        Semantics.DetectableOnWithScalar Q.1.code (toQubitOperator E) c := by
  constructor
  · intro hGenerated
    obtain ⟨p, hScalar⟩ :=
      scalar_action_on_code_of_inGeneratedGroupUpToSign Q E hGenerated
    refine ⟨binaryPhaseScalar p, ?_, ?_⟩
    · by_cases hp : p = 0
      · simp [hp]
      · simp [binaryPhaseScalar, hp]
    · intro ψ hψ φ hφ
      rw [hScalar φ hφ]
      simp
  · rintro ⟨c, hc, hScalar⟩
    have hDetectable :
        Semantics.DetectableOn Q.1.code (toQubitOperator E) :=
      ⟨c, hScalar⟩
    rcases
        (detectableOn_toQubitOperator_iff_inGeneratedGroupUpToSign_or_not_inBinaryNormalizer
          Q E).1 hDetectable with hGenerated | hOutsideNormalizer
    · exact hGenerated
    · obtain ⟨ψ, hψ, hψne⟩ := exists_nonzero_mem_code Q
      have hProduct : c * inner Complex ψ ψ = 0 := by
        rw [← hScalar ψ hψ ψ hψ]
        exact matrixElement_eq_zero_of_not_inBinaryNormalizer
          Q E hOutsideNormalizer ψ hψ ψ hψ
      have hInnerZero : inner Complex ψ ψ = 0 :=
        (mul_eq_zero.mp hProduct).resolve_left hc
      exact False.elim (hψne (inner_self_eq_zero.mp hInnerZero))
end QEC.Coding.StabilizerCode
