-- Prove2me | solution 1 for QEC.Coding.why24QuditQubitUnitary_conjZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:37:55.428324+00:00
-- url     : https://prove2.me/submissions/746338c5-f0ad-40bf-a3b0-6e4a72df6cab

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Theorems.Thm_QEC_Coding_f1024SelectedCoordinates_label_symm
import Theorems.Thm_QEC_Coding_why24QuditZ_apply
import Theorems.Thm_QEC_Coding_f1024SelectedCoordinates_trace_pairing
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

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution (γ : F1024) :
    why24QuditQubitUnitary.conjOperator (why24QuditZ γ) =
      Semantics.Qubit.localZSupport
        (PauliSymplectic.binarySupport (f1024SelectedCoordinates γ)) := by
  ext ψ bits
  rw [Semantics.UnitaryTransport.conjOperator_apply]
  change why24QuditQubitBasisIsometry
      (why24QuditZ γ (why24QuditQubitBasisIsometry.symm ψ)) bits =
        Semantics.Qubit.localZSupport
          (PauliSymplectic.binarySupport (f1024SelectedCoordinates γ)) ψ bits
  rw [why24QuditQubitBasisIsometry_apply, why24QuditZ_apply,
    why24QuditQubitBasisIsometry_symm_apply, Semantics.Qubit.localZSupport_apply]
  simp only [Equiv.apply_symm_apply]
  congr 1
  calc
    PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024
          (γ * why24ComputationalLabelEquiv.symm bits)) =
        PauliSymplectic.binaryPhaseScalar
          (wordPairing (F := ZMod 2) (ι := Fin 10)
            (f1024SelectedCoordinates γ)
            (f1024SelectedCoordinates (why24ComputationalLabelEquiv.symm bits))) := by
              rw [f1024SelectedCoordinates_trace_pairing]
    _ = PauliSymplectic.binaryPhaseScalar
          (wordPairing (F := ZMod 2) (ι := Fin 10)
            (f1024SelectedCoordinates γ)
            (PauliSymplectic.bitstringWordEquiv (Fin 10) bits)) := by
              rw [f1024SelectedCoordinates_label_symm]
    _ = Semantics.Qubit.zSupportPhase
          (PauliSymplectic.binarySupport (f1024SelectedCoordinates γ)) bits := by
              exact (PauliSymplectic.zSupportPhase_eq_binaryPhaseScalar_wordPairing
                (f1024SelectedCoordinates γ) bits).symm
end QEC.Coding
