-- Prove2me | solution 1 for QEC.QLDPC.chainComplexCSSFamily_isLDPC_of_uniform_row_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:09:47.563377+00:00
-- url     : https://prove2.me/submissions/c2ece81c-a816-41c9-9e75-74d778fdfb32

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
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
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowChecks_generate_stabilizerGroup
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowChecks_qubitCheckDegree_le_incidence
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
open QEC.QLDPC
open scoped Classical
universe u w
namespace QEC.QLDPC
theorem _root_.solution
    {A : Type u} {ι κ lambda : A → Type w}
    [∀ a, Fintype (ι a)]
    [∀ a, Fintype (κ a)] [∀ a, Fintype (lambda a)]
    (K : ∀ a, Coding.ChainComplexData
      (ZMod 2) (Coding.Word (ZMod 2) (κ a))
      (Coding.Word (ZMod 2) (ι a))
      (Coding.Word (ZMod 2) (lambda a)))
    {w : Nat}
    (hrowX : ∀ a k, Coding.HammingWeight
      (Coding.wordLinearMapTranspose (K a).boundary1
        (Pi.single k (1 : ZMod 2))) ≤ w)
    (hrowZ : ∀ a l, Coding.HammingWeight
      ((K a).boundary2 (Pi.single l (1 : ZMod 2))) ≤ w)
    (hdegree : ∀ a q,
      ((chainComplexBoundaryIncidence (K a)).variableSupport q).card ≤ w) :
    IsLDPCStabilizerFamily
      (fun a => (K a).binaryCSSSourceValidStabilizer) := by
  refine ⟨w, fun a => ?_⟩
  refine ⟨chainComplexCSSRowChecks (K a), ?_, ?_, ?_⟩
  · simpa [Coding.ChainComplexData.binaryCSSSourceValidStabilizer] using
      chainComplexCSSRowChecks_generate_stabilizerGroup (K a)
  · intro g hg
    rcases (mem_chainComplexCSSRowChecks (K a) g).1 hg with ⟨c, rfl⟩
    cases c with
    | inl k =>
        rw [chainComplexCSSRowCheck_weight_inl]
        exact hrowX a k
    | inr l =>
        rw [chainComplexCSSRowCheck_weight_inr]
        exact hrowZ a l
  · intro q
    exact (chainComplexCSSRowChecks_qubitCheckDegree_le_incidence (K a) q).trans
      (hdegree a q)
end QEC.QLDPC
