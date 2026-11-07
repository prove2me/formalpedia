-- Prove2me | solution 1 for QEC.Coding.f1024SelectedCoordinates_trace_pairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:36:10.191905+00:00
-- url     : https://prove2.me/submissions/26e59649-ff1a-4a4b-b550-611c9352a303

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Theorems.Thm_QEC_Coding_why24QuditZ_apply
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_f1024SelectedSelfDualBasis_traceDual
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
theorem _root_.solution (γ η : F1024) :
    Algebra.trace (ZMod 2) F1024 (γ * η) =
      wordPairing (F := ZMod 2) (ι := Fin 10)
        (f1024SelectedCoordinates γ) (f1024SelectedCoordinates η) := by
  let basis := f1024SelectedSelfDualBasis
  have hcoordinate (x : F1024) (i : Fin 10) :
      Algebra.trace (ZMod 2) F1024 (x * basis i) = f1024SelectedCoordinates x i := by
    calc
      Algebra.trace (ZMod 2) F1024 (x * basis i) =
          (basis.traceDual).repr x i := by
            simpa only [Algebra.traceForm_apply] using
              (Module.Basis.traceDual_repr_apply basis x i).symm
      _ = basis.repr x i := by
            rw [show basis.traceDual = basis from f1024SelectedSelfDualBasis_traceDual]
      _ = f1024SelectedCoordinates x i := rfl
  have hsum : ∑ i : Fin 10, f1024SelectedCoordinates η i • basis i = η :=
    basis.sum_repr η
  calc
    Algebra.trace (ZMod 2) F1024 (γ * η) =
        Algebra.trace (ZMod 2) F1024
          (γ * ∑ i : Fin 10, f1024SelectedCoordinates η i • basis i) := by
            rw [hsum]
    _ = ∑ i : Fin 10,
        f1024SelectedCoordinates η i *
          Algebra.trace (ZMod 2) F1024 (γ * basis i) := by
            rw [Finset.mul_sum, map_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [Algebra.smul_def]
            rw [show γ *
                (algebraMap (ZMod 2) F1024 (f1024SelectedCoordinates η i) * basis i) =
                algebraMap (ZMod 2) F1024 (f1024SelectedCoordinates η i) *
                  (γ * basis i) by ring]
            rw [← Algebra.smul_def]
            exact (Algebra.trace (ZMod 2) F1024).map_smul _ _
    _ = ∑ i : Fin 10,
        f1024SelectedCoordinates γ i * f1024SelectedCoordinates η i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hcoordinate]
            exact mul_comm _ _
    _ = wordPairing (F := ZMod 2) (ι := Fin 10)
        (f1024SelectedCoordinates γ) (f1024SelectedCoordinates η) := by
            rfl
end QEC.Coding
