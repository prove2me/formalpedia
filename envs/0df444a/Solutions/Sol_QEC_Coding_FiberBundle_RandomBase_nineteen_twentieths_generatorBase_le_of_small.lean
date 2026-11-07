-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.nineteen_twentieths_generatorBase_le_of_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:01:04.114867+00:00
-- url     : https://prove2.me/submissions/886c3812-f9c6-42d0-8075-cfbdd94d85ec

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_hitProbability_lower_of_small
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
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r) :
    (19 : NNReal) / 20 *
          (1 -
            (1 - incidenceProbability (4 * r) Delta : NNReal) ^ S.card) +
        (1 - incidenceProbability (4 * r) Delta : NNReal) ^ S.card ≤
      1 -
        (1 : NNReal) / 20 *
          ((399997 : NNReal) / 400000 *
            ((S.card : NNReal) *
              incidenceProbability (4 * r) Delta)) := by
  let avoid : NNReal :=
    (1 - incidenceProbability (4 * r) Delta : NNReal) ^ S.card
  let hit : NNReal := 1 - avoid
  let load : NNReal :=
    (S.card : NNReal) * incidenceProbability (4 * r) Delta
  let penalty : NNReal :=
    (1 : NNReal) / 20 * ((399997 : NNReal) / 400000 * load)
  have hAvoid : avoid ≤ 1 := by
    dsimp [avoid]
    exact pow_le_one₀ (by positivity) (by simp)
  have hHit : (399997 : NNReal) / 400000 * load ≤ hit := by
    exact hitProbability_lower_of_small
      r Delta hr hDelta S hSmall
  have honeTwentieth : (1 : NNReal) / 20 ≤ 1 := by
    apply div_le_one_of_le₀
    · norm_num
    · exact bot_le
  have hPenaltyHit : penalty ≤ hit := by
    calc
      penalty ≤ 1 * ((399997 : NNReal) / 400000 * load) := by
        dsimp [penalty]
        gcongr
      _ = _ := by simp
      _ ≤ hit := hHit
  have hPenaltyOne : penalty ≤ 1 :=
    hPenaltyHit.trans tsub_le_self
  change (19 : NNReal) / 20 * hit + avoid ≤ 1 - penalty
  apply (le_tsub_iff_left hPenaltyOne).2
  calc
    penalty + ((19 : NNReal) / 20 * hit + avoid) ≤
        (1 : NNReal) / 20 * hit +
          ((19 : NNReal) / 20 * hit + avoid) := by
      have hScaled :
          (1 : NNReal) / 20 *
              ((399997 : NNReal) / 400000 * load) ≤
            (1 : NNReal) / 20 * hit :=
        mul_le_mul_of_nonneg_left hHit (by positivity)
      have hPenaltyScaled :
          penalty ≤ (1 : NNReal) / 20 * hit := by
        simpa only [penalty] using hScaled
      simpa only [add_comm] using
        add_le_add_right hPenaltyScaled
          ((19 : NNReal) / 20 * hit + avoid)
    _ = (((1 : NNReal) / 20) + 19 / 20) * hit + avoid := by
      ring
    _ = hit + avoid := by norm_num
    _ = 1 := by
      exact tsub_add_cancel_of_le hAvoid
end QEC.Coding.FiberBundle.RandomBase
