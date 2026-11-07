-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.linearDistance_failureMass_le_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:26:55.153435+00:00
-- url     : https://prove2.me/submissions/aa4b379d-a440-4856-abf1-d95bc4330354

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_supportWord_mem_code_eventMass
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_supportWord_mem_code_eventMass_medium_geometric_le
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_supportWord_mem_code_eventMass_veryLarge_le
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_lowWeightSupport_card_cast_le
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_sum_lowWeightSupport_pow_card_le_nonempty
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_sum_nonemptyVariableSupport_pow_card
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_linearDistance_failureMass_le_exact_sum
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
    (r Delta : Nat) (hr : 0 < r)
    (hDelta : Delta ≤ 4 * r) (hHalf : 2 * Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (@HasLinearDistance r) ≤
      (1 + ENNReal.ofReal
        (Real.exp (-(3 : Real) * Delta / 28))) ^ (4 * r) - 1 +
      ((3 : ENNReal) ^ ((4 * r) / 5) *
        ((4 : ENNReal) / 3) ^ (4 * r)) *
        (ENNReal.ofReal ((172 : Real) / 343)) ^ (3 * r) := by
  let t : ENNReal :=
    ENNReal.ofReal (Real.exp (-(3 : Real) * Delta / 28))
  let c : ENNReal :=
    (ENNReal.ofReal ((172 : Real) / 343)) ^ (3 * r)
  calc
    _ ≤
        ∑ A : LowWeightSupport r,
          (ENNReal.ofReal
            ((1 +
              (1 - 2 * (incidenceProbability (4 * r) Delta).toReal) ^
                A.1.card) / 2)) ^ (3 * r) :=
      linearDistance_failureMass_le_exact_sum r Delta hDelta
    _ = ∑ A : LowWeightSupport r,
        eventMass
          (distribution r Delta hDelta)
          (fun sample => supportWord A.1 ∈ (code sample).carrier) := by
      apply Fintype.sum_congr
      intro A
      exact (supportWord_mem_code_eventMass r Delta hDelta A.1).symm
    _ ≤ ∑ A : LowWeightSupport r, (t ^ A.1.card + c) := by
      apply Finset.sum_le_sum
      intro A _
      by_cases hmedium : A.1.card * Delta ≤ 12 * r
      · exact
          (supportWord_mem_code_eventMass_medium_geometric_le
            r Delta hr hDelta hHalf A.1 hmedium).trans
            (le_add_right le_rfl)
      · have hlarge : 12 * r ≤ A.1.card * Delta :=
          (Nat.lt_of_not_ge hmedium).le
        exact
          (supportWord_mem_code_eventMass_veryLarge_le
            r Delta hr hDelta hHalf A.1 hlarge).trans
            (le_add_left le_rfl)
    _ =
        (∑ A : LowWeightSupport r, t ^ A.1.card) +
          ∑ _A : LowWeightSupport r, c := by
      exact Finset.sum_add_distrib
    _ ≤
        ((1 + t) ^ (4 * r) - 1) +
          ((3 : ENNReal) ^ ((4 * r) / 5) *
            ((4 : ENNReal) / 3) ^ (4 * r)) * c := by
      gcongr
      · exact (sum_lowWeightSupport_pow_card_le_nonempty r t).trans_eq
          (sum_nonemptyVariableSupport_pow_card r t)
      · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        gcongr
        exact lowWeightSupport_card_cast_le r
    _ = _ := rfl
end QEC.Coding.FiberBundle.RandomBase
