-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.inGeneratedGroupUpToSign_of_detectableOn_of_inBinaryNormalizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:44:30.722337+00:00
-- url     : https://prove2.me/submissions/157c62ad-a6e5-46f4-be08-c831d77b4609

import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Symplectic
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_Stabilizer_Detectability
import Theorems.Thm_QEC_Coding_StabilizerCode_toQubitOperator_mem_code_of_inBinaryNormalizer
import Theorems.Thm_QEC_Coding_StabilizerCode_toQubitOperator_ne_zero_of_ne_zero
import Theorems.Thm_QEC_Coding_StabilizerCode_scalar_action_on_code_of_detectableOn_of_inBinaryNormalizer
import Theorems.Thm_QEC_Coding_StabilizerCode_exists_normalizer_anticommuting_witness_on_code
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
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
    (hN : Q.1.InBinaryNormalizer E)
    (hdet : Semantics.DetectableOn Q.1.code (toQubitOperator E)) :
    Q.1.InGeneratedGroupUpToSign E := by
  by_contra hnotS
  obtain ⟨F, ψ, hFN, hψ, hψne, hNotCommutes⟩ :=
    exists_normalizer_anticommuting_witness_on_code Q E hN hnotS
  obtain ⟨c, hscalar⟩ :=
    scalar_action_on_code_of_detectableOn_of_inBinaryNormalizer Q E hN hdet
  have hFψmem : toQubitOperator F ψ ∈ Q.1.code.carrier :=
    toQubitOperator_mem_code_of_inBinaryNormalizer Q hFN hψ
  have hFψne : toQubitOperator F ψ ≠ 0 :=
    toQubitOperator_ne_zero_of_ne_zero F hψne
  have hanti := toQubitOperator_anticommute_of_not_commutes E F hNotCommutes
  have hcNeg : c • toQubitOperator F ψ = -(c • toQubitOperator F ψ) := by
    calc
      c • toQubitOperator F ψ = toQubitOperator E (toQubitOperator F ψ) :=
        (hscalar (toQubitOperator F ψ) hFψmem).symm
      _ = -(toQubitOperator F (toQubitOperator E ψ)) := by
        have happly := congrArg
          (fun A : Semantics.Operator (Semantics.Qubit.QubitRegister ι) => A ψ) hanti
        simpa [Module.End.mul_apply] using happly
      _ = -(c • toQubitOperator F ψ) := by
        rw [hscalar ψ hψ]
        simp
  have hAdd : c • toQubitOperator F ψ + c • toQubitOperator F ψ = 0 :=
    eq_neg_iff_add_eq_zero.mp hcNeg
  have hTwoSmul : ((2 : Complex) * c) • toQubitOperator F ψ = 0 := by
    simpa [add_smul, two_mul, mul_smul] using hAdd
  have hTwoC : (2 : Complex) * c = 0 :=
    (smul_eq_zero.mp hTwoSmul).resolve_right hFψne
  have hcZero : c = 0 := (mul_eq_zero.mp hTwoC).resolve_left (by norm_num)
  have hEψne : toQubitOperator E ψ ≠ 0 :=
    toQubitOperator_ne_zero_of_ne_zero E hψne
  apply hEψne
  rw [hscalar ψ hψ, hcZero]
  simp
end QEC.Coding.StabilizerCode
