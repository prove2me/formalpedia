-- Prove2me | solution 1 for QEC.Coding.why24QuditQubitUnitary_conjPauli
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:39:31.433366+00:00
-- url     : https://prove2.me/submissions/0dac4a1b-22e4-440d-b263-7679525d4819

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Theorems.Thm_QEC_Coding_why24QuditZ_apply
import Theorems.Thm_QEC_Coding_why24QuditQubitUnitary_conjX
import Theorems.Thm_QEC_Coding_why24QuditQubitUnitary_conjZ
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
private theorem why24QuditQubitUnitary_conj_smul
    (c : Complex) (A : Semantics.Operator Why24QuditSpace) :
    why24QuditQubitUnitary.conjOperator (c • A) =
      c • why24QuditQubitUnitary.conjOperator A := by
  ext ψ
  simp [Semantics.UnitaryTransport.conjOperator, smul_eq_mul]
end QEC.Coding
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution (P : Why24FieldPauli) :
    why24QuditQubitUnitary.conjOperator (why24FieldPauliOperator P) =
      why24BinaryPauliOperator (why24PauliLabelEquiv P) := by
  rcases P with ⟨a, β, γ⟩
  change why24QuditQubitUnitary.conjOperator
      (why24PauliPhase a • (why24QuditX β * why24QuditZ γ)) =
        why24PauliPhase a •
          (Semantics.Qubit.localXSupport
              (PauliSymplectic.binarySupport (f1024SelectedCoordinates β)) *
            Semantics.Qubit.localZSupport
              (PauliSymplectic.binarySupport (f1024SelectedCoordinates γ)))
  rw [why24QuditQubitUnitary_conj_smul,
    Semantics.UnitaryTransport.conjOperator_mul, why24QuditQubitUnitary_conjX,
    why24QuditQubitUnitary_conjZ]
end QEC.Coding
