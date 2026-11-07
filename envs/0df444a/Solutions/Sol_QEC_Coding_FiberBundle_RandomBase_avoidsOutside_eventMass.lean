-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.avoidsOutside_eventMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:27:54.792265+00:00
-- url     : https://prove2.me/submissions/07e81af6-61ed-4071-b9da-0c6028f3412b

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_card_constrainedEdges
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_bernoulli_false_eventMass
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_bernoulli_true_eventMass
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_eventMass_congr
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_eventMass_independentProduct_forall
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
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    eventMass
        (distribution r Delta hDelta)
        (AvoidsOutside S T) =
      (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
        (S.card * (4 * r - T.card))) := by
  classical
  let coordinateEvent :
      (Fin (3 * r) × Fin (4 * r)) → Bool → Prop :=
    fun edge bit =>
      if edge.1 ∈ S ∧ edge.2 ∉ T then bit = false else True
  calc
    _ = ∏ edge : Fin (3 * r) × Fin (4 * r),
        eventMass
          (PMF.bernoulli
            (incidenceProbability (4 * r) Delta)
            (incidenceProbability_le_one hDelta))
          (coordinateEvent edge) := by
      rw [distribution]
      exact eventMass_independentProduct_forall
        (fun _ : Fin (3 * r) × Fin (4 * r) =>
          PMF.bernoulli
            (incidenceProbability (4 * r) Delta)
            (incidenceProbability_le_one hDelta))
        coordinateEvent
    _ = ∏ edge : Fin (3 * r) × Fin (4 * r),
        if edge.1 ∈ S ∧ edge.2 ∉ T then
          ((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal)
        else 1 := by
      apply Fintype.prod_congr
      intro edge
      by_cases hConstraint : edge.1 ∈ S ∧ edge.2 ∉ T
      · rw [if_pos hConstraint]
        calc
          eventMass
              (PMF.bernoulli
                (incidenceProbability (4 * r) Delta)
                (incidenceProbability_le_one hDelta))
              (coordinateEvent edge) =
            eventMass
              (PMF.bernoulli
                (incidenceProbability (4 * r) Delta)
                (incidenceProbability_le_one hDelta))
              (fun bit => bit = false) := by
            apply eventMass_congr
            intro bit
            dsimp [coordinateEvent]
            rw [if_pos hConstraint]
          _ = _ := bernoulli_false_eventMass
            (incidenceProbability (4 * r) Delta)
            (incidenceProbability_le_one hDelta)
      · rw [if_neg hConstraint]
        calc
          eventMass
              (PMF.bernoulli
                (incidenceProbability (4 * r) Delta)
                (incidenceProbability_le_one hDelta))
              (coordinateEvent edge) =
            eventMass
              (PMF.bernoulli
                (incidenceProbability (4 * r) Delta)
                (incidenceProbability_le_one hDelta))
              (fun _bit => True) := by
            apply eventMass_congr
            intro bit
            dsimp [coordinateEvent]
            rw [if_neg hConstraint]
          _ = _ := bernoulli_true_eventMass
            (incidenceProbability (4 * r) Delta)
            (incidenceProbability_le_one hDelta)
    _ = ∏ edge ∈
        (Finset.univ.filter fun edge : Fin (3 * r) × Fin (4 * r) =>
          edge.1 ∈ S ∧ edge.2 ∉ T),
        ((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) := by
      rw [Finset.prod_ite]
      simp
    _ = _ := by
      rw [Finset.prod_const, card_constrainedEdges]
end QEC.Coding.FiberBundle.RandomBase
