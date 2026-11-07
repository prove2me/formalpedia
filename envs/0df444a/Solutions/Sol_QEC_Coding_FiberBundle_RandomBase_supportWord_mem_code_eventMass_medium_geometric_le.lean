-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.supportWord_mem_code_eventMass_medium_geometric_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:23:21.5002+00:00
-- url     : https://prove2.me/submissions/d1a5a136-9636-4733-9b41-3839e432d5a1

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_supportWord_mem_code_eventMass
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_parityProbabilityBase_medium_le
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_check_expected_degree
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_multipleRotation_val
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
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
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.columnDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.groupedDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.independentProduct_apply
attribute [local simp] QEC.Coding.FiberBundle.multipleRotation_val
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
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
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r)
    (A : Finset (Fin (4 * r))) (hmedium : A.card * Delta ≤ 12 * r) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => supportWord A ∈ (code sample).carrier) ≤
      (ENNReal.ofReal
        (Real.exp (-(3 : Real) * Delta / 28))) ^ A.card := by
  let p : Real := (incidenceProbability (4 * r) Delta).toReal
  have hmean : ((4 * r : Nat) : Real) * p = Delta := by
    exact check_expected_degree r Delta hr
  have hp : p = (Delta : Real) / ((4 * r : Nat) : Real) := by
    apply (eq_div_iff (by positivity : (((4 * r : Nat) : Real) ≠ 0))).2
    simpa [mul_comm] using hmean
  have hp0 : 0 ≤ p := by positivity
  have hpHalf : p ≤ 1 / 2 := by
    rw [hp, div_le_iff₀ (by positivity : (0 : Real) < (4 * r : Nat))]
    have hHalfR : ((2 * Delta : Nat) : Real) ≤ (4 * r : Nat) := by
      exact_mod_cast hHalf
    norm_num [Nat.cast_mul] at hHalfR ⊢
    linarith
  have hmediumR : p * A.card ≤ 3 := by
    rw [hp]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity :
      (0 : Real) < (4 * r : Nat))]
    have hcast :
        (((Delta * A.card : Nat) : Real) ≤ ((12 * r : Nat) : Real)) := by
      exact_mod_cast (show Delta * A.card ≤ 12 * r by
        simpa [Nat.mul_comm] using hmedium)
    norm_num [Nat.cast_mul] at hcast ⊢
    linarith
  rw [supportWord_mem_code_eventMass r Delta hDelta A]
  calc
    _ ≤
        (ENNReal.ofReal
          (Real.exp (-(p * A.card) / 7))) ^ (3 * r) := by
      apply pow_le_pow_left'
      exact ENNReal.ofReal_le_ofReal
        (parityProbabilityBase_medium_le
          p A.card hp0 hpHalf hmediumR)
    _ = ENNReal.ofReal
        ((Real.exp (-(p * A.card) / 7)) ^ (3 * r)) := by
      rw [ENNReal.ofReal_pow (Real.exp_pos _).le]
    _ = ENNReal.ofReal
        ((Real.exp (-(3 : Real) * Delta / 28)) ^ A.card) := by
      congr 1
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      congr 1
      calc
        ((3 * r : Nat) : Real) * (-(p * (A.card : Real)) / 7) =
            (-(3 : Real) * (A.card : Real) / 28) *
              (((4 * r : Nat) : Real) * p) := by
                norm_num [Nat.cast_mul]
                ring
        _ = (-(3 : Real) * (A.card : Real) / 28) * Delta := by
          rw [hmean]
        _ = (A.card : Real) * (-(3 : Real) * Delta / 28) := by ring
    _ = _ := ENNReal.ofReal_pow (Real.exp_pos _).le A.card
end QEC.Coding.FiberBundle.RandomBase
