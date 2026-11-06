-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.generatedGroup_pairwise_commutes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:27:59.126008+00:00
-- url     : https://prove2.me/submissions/e9ced88a-ca58-400f-a796-466ff5ecb0dd

import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Symplectic
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_Stabilizer_Detectability
import Theorems.Thm_QEC_Coding_PauliSymplectic_commutes_comm
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_commutes_binaryDagger_right
import Theorems.Thm_QEC_Coding_PauliSymplectic_commutes_binaryMul_right
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


section
noncomputable section
namespace QEC
namespace Coding
universe u
namespace PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
end PauliSymplectic
namespace StabilizerCode
open PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
private theorem commutes_generatedGroup_right_of_mem_stabilizers
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    {P : Binary ι} (hP : P ∈ Q.stabilizers) {R : Binary ι}
    (hR : R ∈ Q.generatedGroup) : Commutes P R := by
  classical
  letI : Fintype {S : Binary ι // S ∈ Q.stabilizers} := Fintype.ofFinite _
  unfold generatedGroup at hR
  simp only [Set.mem_setOf_eq] at hR
  induction hR with
  | one => exact commutes_binaryOne_right P
  | generator check => exact Q.isotropic P hP check.1 check.2
  | mul _ _ ihP ihR => exact commutes_binaryMul_right ihP ihR
  | dagger _ ihP => exact commutes_binaryDagger_right ihP
end StabilizerCode
end Coding
end QEC
end
end

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
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    {P R : Binary ι} (hP : P ∈ Q.generatedGroup) (hR : R ∈ Q.generatedGroup) :
    Commutes P R := by
  classical
  letI : Fintype {S : Binary ι // S ∈ Q.stabilizers} := Fintype.ofFinite _
  unfold generatedGroup at hP
  simp only [Set.mem_setOf_eq] at hP
  induction hP with
  | one => exact (commutes_comm _ _).2 (commutes_binaryOne_right R)
  | generator check =>
      exact commutes_generatedGroup_right_of_mem_stabilizers Q check.2 hR
  | @mul P S _ _ ihP ihS =>
      apply (commutes_comm (binaryMul P S) R).2
      exact commutes_binaryMul_right
        ((commutes_comm P R).1 ihP) ((commutes_comm S R).1 ihS)
  | @dagger P _ ihP =>
      simpa [Commutes, binaryDagger] using ihP
end QEC.Coding.StabilizerCode
