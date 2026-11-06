-- Prove2me | solution 1 for QEC.Locality.EdgeRestrictedStoppedRecursion.refinedEdgeActive_card_mul_budget_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:48:17.033183+00:00
-- url     : https://prove2.me/submissions/03cee8ba-f517-435d-bf1b-f0f544234c48

import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
import Definitions.Def_QEC_Locality_SeparatorProfile_Completion
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_edgeOwnerType_card_eq_terminalOwnerCount
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_edgeOwnerType_card_eq_terminalOwnerCount
import Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_terminalOwnerCount_mul_budget_le
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
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Locality.MarkedSeparatorSpine.exposedSide_stop
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
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


section
namespace QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
private theorem EdgeRestrictedStoppedRecursion.refinedOwnerType_card_mul_budget_le
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent) :
    Fintype.card (tree.refinedOwnerType beta exponent hProfile) *
        weightedSpineSeparatorBudget beta exponent r ≤
      tree.terminalOwnerCount * weightedSpineSeparatorBudget beta exponent r +
        2 * tree.terminalBoundaryMass := by
  classical
  let budget := weightedSpineSeparatorBudget beta exponent r
  calc
    Fintype.card (tree.refinedOwnerType beta exponent hProfile) * budget =
        (∑ outer : tree.edgeOwnerType,
          Fintype.card (tree.weightedRefinementAt beta exponent hProfile outer).edgeOwnerType) *
          budget := by
      change Fintype.card (Sigma fun outer : tree.edgeOwnerType =>
        (tree.weightedRefinementAt beta exponent hProfile outer).edgeOwnerType) * budget = _
      rw [Fintype.card_sigma]
    _ = ∑ outer : tree.edgeOwnerType,
        Fintype.card (tree.weightedRefinementAt beta exponent hProfile outer).edgeOwnerType *
          budget := Finset.sum_mul _ _ _
    _ ≤ ∑ outer : tree.edgeOwnerType,
        (budget + 2 * (tree.terminalBoundary outer).card) := by
      apply Finset.sum_le_sum
      intro outer _
      rw [(tree.weightedRefinementAt beta exponent hProfile outer)
        |>.edgeOwnerType_card_eq_terminalOwnerCount]
      exact (tree.weightedRefinementAt beta exponent hProfile outer)
        |>.terminalOwnerCount_mul_budget_le
    _ = Fintype.card tree.edgeOwnerType * budget + 2 * tree.terminalBoundaryMass := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.cast_id, ← Finset.mul_sum, terminalBoundaryMass, Nat.mul_comm]
    _ = tree.terminalOwnerCount * budget + 2 * tree.terminalBoundaryMass := by
      rw [tree.edgeOwnerType_card_eq_terminalOwnerCount]
end QEC.Locality
end

set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
namespace EdgeRestrictedStoppedRecursion
theorem _root_.solution
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent) :
    (tree.refinedEdgeActive beta exponent hProfile).card *
        weightedSpineSeparatorBudget beta exponent r ≤
      tree.terminalOwnerCount * weightedSpineSeparatorBudget beta exponent r +
        2 * tree.terminalBoundaryMass := by
  exact (Nat.mul_le_mul_right _
    (show (tree.refinedEdgeActive beta exponent hProfile).card ≤
        Fintype.card (tree.refinedOwnerType beta exponent hProfile) by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.filter_subset _ _))).trans
    (tree.refinedOwnerType_card_mul_budget_le beta exponent hProfile)
end EdgeRestrictedStoppedRecursion
end QEC.Locality
