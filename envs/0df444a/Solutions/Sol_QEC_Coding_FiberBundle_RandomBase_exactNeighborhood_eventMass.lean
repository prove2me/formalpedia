-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.exactNeighborhood_eventMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:01:03.084801+00:00
-- url     : https://prove2.me/submissions/78f9ec88-6738-4ac3-8911-3d4ed9955058

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnAvoids_eventMass
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnHits_eventMass
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_checkSetNeighborhood_eq_iff_groupedExactNeighborhood
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply_eq_grouped
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_eventMass_congr
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_eventMass_decidable_irrel
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_eventMass_equiv
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
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => checkSetNeighborhood sample S = T) =
      (1 -
        (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
          S.card)) ^ T.card *
      (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
        S.card) ^ (4 * r - T.card) := by
  classical
  let q : ENNReal :=
    (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
      S.card)
  let coordinateEvent : Fin (4 * r) → ColumnSample r → Prop :=
    fun b column =>
      if b ∈ T then ColumnHits S column else ColumnAvoids S column
  calc
    _ = eventMass
        (groupedDistribution r Delta hDelta)
        (GroupedExactNeighborhood S T) := by
      exact eventMass_equiv
        (sampleEquivGrouped r)
        (distribution r Delta hDelta)
        (groupedDistribution r Delta hDelta)
        (fun sample => checkSetNeighborhood sample S = T)
        (GroupedExactNeighborhood S T)
        (distribution_apply_eq_grouped r Delta hDelta)
        (checkSetNeighborhood_eq_iff_groupedExactNeighborhood · S T)
    _ = ∏ b : Fin (4 * r),
        eventMass
          (columnDistribution r Delta hDelta)
          (coordinateEvent b) := by
      rw [groupedDistribution]
      have hProduct := eventMass_independentProduct_forall
        (fun _ : Fin (4 * r) => columnDistribution r Delta hDelta)
        coordinateEvent
      exact (eventMass_decidable_irrel
        (independentProduct fun _ : Fin (4 * r) =>
          columnDistribution r Delta hDelta)
        (GroupedExactNeighborhood S T)
        _ _).trans hProduct
    _ = ∏ b : Fin (4 * r), if b ∈ T then 1 - q else q := by
      apply Fintype.prod_congr
      intro b
      by_cases hbT : b ∈ T
      · rw [if_pos hbT]
        calc
          eventMass
              (columnDistribution r Delta hDelta)
              (coordinateEvent b) =
            eventMass
              (columnDistribution r Delta hDelta)
              (ColumnHits S) := by
            apply eventMass_congr
            intro column
            dsimp [coordinateEvent]
            rw [if_pos hbT]
          _ = 1 - q := by
            simpa [q] using columnHits_eventMass r Delta hDelta S
      · rw [if_neg hbT]
        calc
          eventMass
              (columnDistribution r Delta hDelta)
              (coordinateEvent b) =
            eventMass
              (columnDistribution r Delta hDelta)
              (ColumnAvoids S) := by
            apply eventMass_congr
            intro column
            dsimp [coordinateEvent]
            rw [if_neg hbT]
          _ = q := by
            simpa [q] using columnAvoids_eventMass r Delta hDelta S
    _ = (1 - q) ^ T.card * q ^ (4 * r - T.card) := by
      have hIn :
          ((Finset.univ : Finset (Fin (4 * r))).filter
            (fun b => b ∈ T)).card = T.card := by
        simp
      have hOut :
          ((Finset.univ : Finset (Fin (4 * r))).filter
            (fun b => b ∉ T)).card = 4 * r - T.card := by
        rw [← Finset.sdiff_eq_filter, Finset.card_sdiff]
        simp
      rw [Finset.prod_ite]
      simp only [Finset.prod_const]
      rw [hIn, hOut]
    _ = _ := rfl
end QEC.Coding.FiberBundle.RandomBase
