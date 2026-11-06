-- Prove2me | solution 1 for QEC.QLDPC.chainComplexBoundaryIncidence_boundedLocality_of_boundary_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:39:01.524209+00:00
-- url     : https://prove2.me/submissions/040d6116-a6af-4aea-abc0-ba0fdbe9863f

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
    {F : Type u} {ι κ lambda : Type v} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : Coding.ChainComplexData F (Coding.Word F κ) (Coding.Word F ι)
      (Coding.Word F lambda))
    {w variableDegree : Nat}
    (hrow1 : ∀ k, Coding.HammingWeight
      (Coding.wordLinearMapTranspose K.boundary1
        (Coding.canonicalBasisWord (F := F) k)) ≤ w)
    (hrow2 : ∀ l, Coding.HammingWeight
      (K.boundary2 (Coding.canonicalBasisWord (F := F) l)) ≤ w)
    (hcol : ∀ q, ((chainComplexBoundaryIncidence K).variableSupport q).card ≤
      variableDegree) :
    Coding.BoundedLocality (chainComplexBoundaryIncidence K).localityProfile
      (max w variableDegree) := by
  refine (chainComplexBoundaryIncidence K).boundedLocality_of_row_col_bounds ?_ ?_
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
end QEC.QLDPC
