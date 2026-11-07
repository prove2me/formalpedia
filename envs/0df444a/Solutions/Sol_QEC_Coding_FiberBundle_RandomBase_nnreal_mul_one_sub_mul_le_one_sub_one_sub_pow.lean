-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.nnreal_mul_one_sub_mul_le_one_sub_one_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:54:52.624452+00:00
-- url     : https://prove2.me/submissions/e250327b-c506-4dad-96fe-1ff6dd9c1446

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
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
    (p : NNReal) (hp : p ≤ 1) (n : Nat) :
    (n : NNReal) * p * (1 - (n : NNReal) * p) ≤
      1 - (1 - p : NNReal) ^ n := by
  let q : NNReal := 1 - p
  have hq_le_one : q ≤ 1 := by
    dsimp [q]
    exact tsub_le_self
  have hqpow_lower :
      1 - (n : NNReal) * p ≤ q ^ n := by
    by_cases hnp : (n : NNReal) * p ≤ 1
    · change
        (((1 - (n : NNReal) * p : NNReal) : Real) ≤
          ((q ^ n : NNReal) : Real))
      rw [NNReal.coe_sub hnp]
      have hBernoulli :
          1 + (n : Real) * ((q : Real) - 1) ≤ (q : Real) ^ n := by
        apply one_add_mul_sub_le_pow
        have hqNonneg : (0 : Real) ≤ q := by positivity
        linarith
      have hqReal : (q : Real) = 1 - (p : Real) := by
        dsimp [q]
        rw [NNReal.coe_sub hp]
        norm_num
      norm_num only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow]
      rw [hqReal] at hBernoulli ⊢
      norm_num at hBernoulli ⊢
      linarith
    · have hnp' : 1 ≤ (n : NNReal) * p := le_of_not_ge hnp
      rw [tsub_eq_zero_of_le hnp']
      exact bot_le
  have hsum_lower :
      (n : NNReal) * q ^ n ≤
        ∑ i ∈ Finset.range n, q ^ i := by
    calc
      (n : NNReal) * q ^ n =
          ∑ _i ∈ Finset.range n, q ^ n := by
            simp [nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.range n, q ^ i := by
        exact Finset.sum_le_sum fun i hi =>
          pow_le_pow_right_of_le_one'
            hq_le_one
            (Nat.le_of_lt (Finset.mem_range.mp hi))
  have hgeom :
      (∑ i ∈ Finset.range n, q ^ i) * p =
        1 - q ^ n := by
    have hqComplement : 1 - q = p := by
      dsimp [q]
      exact tsub_tsub_cancel_of_le hp
    simpa only [hqComplement] using
      (geom_sum_mul_of_le_one hq_le_one n)
  calc
    (n : NNReal) * p * (1 - (n : NNReal) * p) ≤
        (n : NNReal) * p * q ^ n := by
      exact mul_le_mul_of_nonneg_left hqpow_lower (by positivity)
    _ = ((n : NNReal) * q ^ n) * p := by ring
    _ ≤ (∑ i ∈ Finset.range n, q ^ i) * p := by
      exact mul_le_mul_of_nonneg_right hsum_lower (by positivity)
    _ = 1 - q ^ n := hgeom
    _ = 1 - (1 - p : NNReal) ^ n := rfl
end QEC.Coding.FiberBundle.RandomBase
