-- Prove2me | solution 1 for QEC.Coding.why24U_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:21:07.042217+00:00
-- url     : https://prove2.me/submissions/406367af-991a-44ee-bfb0-6618fa46665a

import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
import Theorems.Thm_QEC_Coding_why24U_apply
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_why24QuditZ_apply
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
attribute [local simp] QEC.Coding.why24QuditZ_apply
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


attribute [local simp] QEC.Coding.why24U_apply
section
noncomputable section
namespace QEC.Coding
open scoped BigOperators
private theorem why24_binaryPhaseScalar_conj (p : ZMod 2) :
    star (PauliSymplectic.binaryPhaseScalar p) = PauliSymplectic.binaryPhaseScalar p := by
  by_cases hp : p = 0 <;> simp [PauliSymplectic.binaryPhaseScalar, hp]
private theorem why24U_isSymmetric (β : F1024) (n : ℕ) :
    (why24U β n).IsSymmetric := by
  intro x y
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro η _
  simp only [why24U_apply, RCLike.inner_apply']
  change star (PauliSymplectic.binaryPhaseScalar
      (Algebra.trace (ZMod 2) F1024 (β * η ^ n)) * x η) * y η =
    star (x η) *
      (PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * η ^ n)) * y η)
  rw [star_mul, why24_binaryPhaseScalar_conj]
  ring
end QEC.Coding
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution (β : F1024) (n : ℕ) :
    LinearMap.adjoint (why24U β n) = why24U β n :=
  (why24U_isSymmetric β n).adjoint_eq
end QEC.Coding
