-- Prove2me | solution 1 for QEC.Coding.f1024SelectedCoordinates_label_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:19:41.091379+00:00
-- url     : https://prove2.me/submissions/275b66f8-46e7-47f1-aed3-b0513d5787ca

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Theorems.Thm_QEC_Coding_why24ComputationalLabelEquiv_coordinates
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
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution
    (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    f1024SelectedCoordinates (why24ComputationalLabelEquiv.symm bits) =
      PauliSymplectic.bitstringWordEquiv (Fin 10) bits := by
  calc
    f1024SelectedCoordinates (why24ComputationalLabelEquiv.symm bits) =
        PauliSymplectic.bitstringWordEquiv (Fin 10)
          (why24ComputationalLabelEquiv (why24ComputationalLabelEquiv.symm bits)) :=
      (why24ComputationalLabelEquiv_coordinates _).symm
    _ = PauliSymplectic.bitstringWordEquiv (Fin 10) bits := by simp
end QEC.Coding
