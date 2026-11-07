-- Prove2me | solution 1 for QEC.Coding.why24QuditQubitUnitary_conj_isUnitary_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:26:29.720901+00:00
-- url     : https://prove2.me/submissions/f0404305-f456-4e1f-acc1-2afddfe69f6b

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Theorems.Thm_QEC_Coding_why24QuditZ_apply
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


attribute [local simp] QEC.Coding.why24QuditZ_apply
section
noncomputable section
namespace QEC.Coding
open scoped BigOperators
private theorem why24IsUnitary_conjOperator
    {H K : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K] (U : Semantics.UnitaryTransport H K)
    {C : Semantics.Operator H} (hC : Why24IsUnitary C) :
    Why24IsUnitary (U.conjOperator C) := by
  intro x y
  rw [Semantics.UnitaryTransport.conjOperator_apply,
    Semantics.UnitaryTransport.conjOperator_apply]
  calc
    inner Complex (U (C (U.toLinearEquiv.symm x))) (U (C (U.toLinearEquiv.symm y))) =
        inner Complex (C (U.toLinearEquiv.symm x)) (C (U.toLinearEquiv.symm y)) :=
      U.map_inner _ _
    _ = inner Complex (U.toLinearEquiv.symm x) (U.toLinearEquiv.symm y) :=
      hC _ _
    _ = inner Complex x y :=
      U.symm.map_inner _ _
end QEC.Coding
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution (C : Semantics.Operator Why24QuditSpace) :
    Why24IsUnitary (why24QuditQubitUnitary.conjOperator C) ↔ Why24IsUnitary C := by
  constructor
  · intro hC
    have hback := why24IsUnitary_conjOperator why24QuditQubitUnitary.symm hC
    simpa using hback
  · exact why24IsUnitary_conjOperator why24QuditQubitUnitary
end QEC.Coding
