-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.lowWeightSupport_card_cast_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:10:12.014422+00:00
-- url     : https://prove2.me/submissions/dc45539d-e14b-441d-b5d9-193b8478f8d4

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_lowWeightSupport_card_le
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_sum_powerset_pow_card
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
    (r : Nat) :
    (Fintype.card (LowWeightSupport r) : ENNReal) ≤
      (3 : ENNReal) ^ ((4 * r) / 5) *
        ((4 : ENNReal) / 3) ^ (4 * r) := by
  let k : Nat := (4 * r) / 5
  let x : ENNReal := (1 : ENNReal) / 3
  have hpoint (A : LowWeightSupport r) :
      (1 : ENNReal) ≤ (3 : ENNReal) ^ k * x ^ A.1.card := by
    have hcard : A.1.card ≤ k := lowWeightSupport_card_le A
    have hxle : x ≤ 1 := by
      dsimp [x]
      norm_num
    have hpow : x ^ k ≤ x ^ A.1.card :=
      pow_le_pow_right_of_le_one' hxle hcard
    calc
      (1 : ENNReal) =
          (3 : ENNReal) ^ k * x ^ k := by
            rw [← mul_pow]
            dsimp [x]
            rw [div_eq_mul_inv, one_mul,
              ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
      _ ≤ (3 : ENNReal) ^ k * x ^ A.1.card :=
        by gcongr
  have hsub :
      (∑ A : LowWeightSupport r, x ^ A.1.card) ≤
        ∑ A : Finset (Fin (4 * r)), x ^ A.card := by
    have hsplit :=
      Fintype.sum_subtype_add_sum_subtype
        (fun A : Finset (Fin (4 * r)) =>
          A.Nonempty ∧ 5 * A.card < 4 * r)
        (fun A => x ^ A.card)
    change
      (∑ A : {A : Finset (Fin (4 * r)) //
        A.Nonempty ∧ 5 * A.card < 4 * r}, x ^ A.1.card) ≤
        ∑ A : Finset (Fin (4 * r)), x ^ A.card
    rw [← hsplit]
    exact le_add_right le_rfl
  have hall :
      (∑ A : Finset (Fin (4 * r)), x ^ A.card) =
        (1 + x) ^ (4 * r) := by
    rw [← Finset.powerset_univ]
    simpa only [Fintype.card_fin, Finset.card_univ] using
      (sum_powerset_pow_card
        (Finset.univ : Finset (Fin (4 * r))) x)
  calc
    (Fintype.card (LowWeightSupport r) : ENNReal) =
        ∑ _A : LowWeightSupport r, (1 : ENNReal) := by simp
    _ ≤ ∑ A : LowWeightSupport r,
        (3 : ENNReal) ^ k * x ^ A.1.card := by
      exact Finset.sum_le_sum fun A _ => hpoint A
    _ = (3 : ENNReal) ^ k *
        ∑ A : LowWeightSupport r, x ^ A.1.card := by
      rw [Finset.mul_sum]
    _ ≤ (3 : ENNReal) ^ k *
        ∑ A : Finset (Fin (4 * r)), x ^ A.card :=
      by gcongr
    _ = (3 : ENNReal) ^ k * (1 + x) ^ (4 * r) := by
      rw [hall]
    _ = _ := by
      have hxsum : (1 + x : ENNReal) = 4 / 3 := by
        dsimp [x]
        calc
          (1 + (1 : ENNReal) / 3) =
              3 * 3⁻¹ + 1 * 3⁻¹ := by
                rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
                simp
          _ = (3 + 1) * 3⁻¹ := by rw [add_mul]
          _ = (4 : ENNReal) / 3 := by
            norm_num [div_eq_mul_inv]
      rw [hxsum]
end QEC.Coding.FiberBundle.RandomBase
