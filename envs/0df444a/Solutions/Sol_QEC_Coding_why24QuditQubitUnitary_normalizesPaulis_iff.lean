-- Prove2me | solution 1 for QEC.Coding.why24QuditQubitUnitary_normalizesPaulis_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:41:02.349089+00:00
-- url     : https://prove2.me/submissions/272a99fb-c8cf-4873-979c-a6c982f761b3

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Theorems.Thm_QEC_Coding_why24QuditZ_apply
import Theorems.Thm_QEC_Coding_why24QuditQubitUnitary_conjPauli
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
private theorem why24QuditQubitUnitary_conjOperator_injective
    {A B : Semantics.Operator Why24QuditSpace}
    (h : why24QuditQubitUnitary.conjOperator A = why24QuditQubitUnitary.conjOperator B) :
    A = B := by
  have hback := congrArg (fun T : Semantics.Operator Why24QubitSpace =>
    why24QuditQubitUnitary.symm.conjOperator T) h
  simpa using hback
end QEC.Coding
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution (C : Semantics.Operator Why24QuditSpace) :
    why24BinaryNormalizesPaulis (why24QuditQubitUnitary.conjOperator C) ↔
      why24FieldNormalizesPaulis C := by
  constructor
  · intro hC P
    obtain ⟨Q, hQ⟩ := hC (why24PauliLabelEquiv P)
    refine ⟨why24PauliLabelEquiv.symm Q, ?_⟩
    apply why24QuditQubitUnitary_conjOperator_injective
    calc
      why24QuditQubitUnitary.conjOperator
          (C * why24FieldPauliOperator P * LinearMap.adjoint C) =
          why24QuditQubitUnitary.conjOperator C *
            why24BinaryPauliOperator (why24PauliLabelEquiv P) *
              LinearMap.adjoint (why24QuditQubitUnitary.conjOperator C) := by
            rw [Semantics.UnitaryTransport.conjOperator_mul,
              Semantics.UnitaryTransport.conjOperator_mul,
              Semantics.UnitaryTransport.conjOperator_adjoint,
              why24QuditQubitUnitary_conjPauli]
      _ = why24BinaryPauliOperator Q := hQ
      _ = why24QuditQubitUnitary.conjOperator
          (why24FieldPauliOperator (why24PauliLabelEquiv.symm Q)) := by
            rw [why24QuditQubitUnitary_conjPauli]
            simp
  · intro hC P
    obtain ⟨Q, hQ⟩ := hC (why24PauliLabelEquiv.symm P)
    refine ⟨why24PauliLabelEquiv Q, ?_⟩
    calc
      why24QuditQubitUnitary.conjOperator C * why24BinaryPauliOperator P *
          LinearMap.adjoint (why24QuditQubitUnitary.conjOperator C) =
          why24QuditQubitUnitary.conjOperator C *
            why24QuditQubitUnitary.conjOperator
              (why24FieldPauliOperator (why24PauliLabelEquiv.symm P)) *
              LinearMap.adjoint (why24QuditQubitUnitary.conjOperator C) := by
            rw [why24QuditQubitUnitary_conjPauli]
            simp
      _ = why24QuditQubitUnitary.conjOperator
          (C * why24FieldPauliOperator (why24PauliLabelEquiv.symm P) *
            LinearMap.adjoint C) := by
            rw [Semantics.UnitaryTransport.conjOperator_mul,
              Semantics.UnitaryTransport.conjOperator_mul,
              Semantics.UnitaryTransport.conjOperator_adjoint]
      _ = why24QuditQubitUnitary.conjOperator (why24FieldPauliOperator Q) :=
            congrArg why24QuditQubitUnitary.conjOperator hQ
      _ = why24BinaryPauliOperator (why24PauliLabelEquiv Q) :=
            why24QuditQubitUnitary_conjPauli Q
end QEC.Coding
