-- Prove2me | solution 1 for QEC.QLDPC.exists_binaryChainComplexQLDPCProperty_of_boundary_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:39:12.371199+00:00
-- url     : https://prove2.me/submissions/2de83d39-6853-424d-b578-2441d7a7fb8e

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
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


attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr

set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC
namespace QEC.QLDPC
theorem _root_.solution
    {ι κ lambda : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype lambda]
    (K : Coding.ChainComplexData
      (ZMod 2) (Coding.Word (ZMod 2) κ) (Coding.Word (ZMod 2) ι)
      (Coding.Word (ZMod 2) lambda))
    (parameters : Coding.CodeParameters (ZMod 2) ι)
    {w variableDegree : Nat}
    (hrow1 : ∀ k, Coding.HammingWeight
      (Coding.wordLinearMapTranspose K.boundary1
        (Coding.canonicalBasisWord (F := ZMod 2) k)) ≤ w)
    (hrow2 : ∀ l, Coding.HammingWeight
      (K.boundary2 (Coding.canonicalBasisWord (F := ZMod 2) l)) ≤ w)
    (hcol : ∀ q, ((chainComplexBoundaryIncidence K).variableSupport q).card ≤
      variableDegree) :
    ∃ P : Coding.QLDPCProperty (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)
      (Coding.Word (ZMod 2) κ) (Coding.Word (ZMod 2) ι)
      (Coding.Word (ZMod 2) lambda),
      P.chainCode = K.binaryChainComplexCode ∧
      P.parameters = parameters ∧
      P.locality = (chainComplexBoundaryIncidence K).localityProfile ∧
      P.localityBound = max w variableDegree := by
  refine ⟨QLDPCProperty.ofCheckIncidenceBounds
    K.binaryChainComplexCode parameters (chainComplexBoundaryIncidence K)
    (B := max w variableDegree) ?_ ?_, ?_, ?_, ?_, ?_⟩
  · intro c
    cases c with
    | inl k =>
        rw [chainComplexBoundaryIncidence_checkSupport_inl]
        exact (hrow1 k).trans (Nat.le_max_left w variableDegree)
    | inr l =>
        rw [chainComplexBoundaryIncidence_checkSupport_inr]
        exact (hrow2 l).trans (Nat.le_max_left w variableDegree)
  · intro q
    exact (hcol q).trans (Nat.le_max_right w variableDegree)
  · rfl
  · rfl
  · rfl
  · rfl
end QEC.QLDPC
