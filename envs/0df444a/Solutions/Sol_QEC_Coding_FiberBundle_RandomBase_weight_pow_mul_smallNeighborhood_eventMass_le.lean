-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.weight_pow_mul_smallNeighborhood_eventMass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:06:42.461192+00:00
-- url     : https://prove2.me/submissions/e6444fda-b75d-42ba-aebf-c29013c8c6c7

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_sum_weight_pow_mul_exactNeighborhood_eventMass
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_eventMass_le_sum_eventMass
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
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r))) (cutoff : Nat)
    (weight : ENNReal) (hweight : weight ≤ 1) :
    weight ^ cutoff *
        eventMass
          (distribution r Delta hDelta)
          (fun sample =>
            (checkSetNeighborhood sample S).card ≤ cutoff) ≤
      (weight *
          (1 -
            (((1 - incidenceProbability (4 * r) Delta : NNReal) :
              ENNReal) ^ S.card)) +
        (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
          S.card)) ^ (4 * r) := by
  let exactMass : Finset (Fin (4 * r)) → ENNReal :=
    fun T =>
      eventMass
        (distribution r Delta hDelta)
        (fun sample => checkSetNeighborhood sample S = T)
  calc
    _ ≤ weight ^ cutoff *
        ∑ T : SmallNeighborhood r cutoff, exactMass T.1 := by
      gcongr
      apply eventMass_le_sum_eventMass
      intro sample hsample
      exact
        ⟨⟨checkSetNeighborhood sample S, hsample⟩, rfl⟩
    _ = ∑ T : SmallNeighborhood r cutoff,
        weight ^ cutoff * exactMass T.1 := by
      rw [Finset.mul_sum]
    _ ≤ ∑ T : SmallNeighborhood r cutoff,
        weight ^ T.1.card * exactMass T.1 := by
      exact Finset.sum_le_sum fun T _ => by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_right_of_le_one' hweight T.2)
          (by positivity)
    _ ≤ ∑ T : Finset (Fin (4 * r)),
        weight ^ T.card * exactMass T := by
      have hsplit :=
        Fintype.sum_subtype_add_sum_subtype
          (fun T : Finset (Fin (4 * r)) => T.card ≤ cutoff)
          (fun T => weight ^ T.card * exactMass T)
      rw [← hsplit]
      exact le_add_right le_rfl
    _ = _ := by
      dsimp only [exactMass]
      exact sum_weight_pow_mul_exactNeighborhood_eventMass
        r Delta hDelta S weight
end QEC.Coding.FiberBundle.RandomBase
