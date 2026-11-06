-- Prove2me | solution 1 for QEC.QLDPC.generatedStabilizer_cssXCheck_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:27:50.458773+00:00
-- url     : https://prove2.me/submissions/1bfa25bd-ef4d-4ef8-a913-56b0e87af03e

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
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
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC
namespace QEC.QLDPC
theorem _root_.solution
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {κ : Type v} [Fintype κ] {alpha : Type w}
    (generators : κ → Coding.PauliSymplectic.Binary ι)
    (s : Finset alpha) (f : alpha → Coding.Word (ZMod 2) ι)
    (h : ∀ a ∈ s, Coding.PauliSymplectic.GeneratedStabilizer generators
      (Coding.PauliSymplectic.cssXCheck (f a))) :
    Coding.PauliSymplectic.GeneratedStabilizer generators
      (Coding.PauliSymplectic.cssXCheck (∑ a ∈ s, f a)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa [Coding.PauliSymplectic.binaryOne] using
        (Coding.PauliSymplectic.GeneratedStabilizer.one (generators := generators))
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      rw [← Coding.PauliSymplectic.binaryMul_cssXCheck]
      exact Coding.PauliSymplectic.GeneratedStabilizer.mul
        (h a (Finset.mem_insert_self a s))
        (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))
end QEC.QLDPC
