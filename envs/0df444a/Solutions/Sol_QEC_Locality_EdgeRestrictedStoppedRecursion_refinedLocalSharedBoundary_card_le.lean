-- Prove2me | solution 1 for QEC.Locality.EdgeRestrictedStoppedRecursion.refinedLocalSharedBoundary_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:51:17.970197+00:00
-- url     : https://prove2.me/submissions/0279a0c4-a554-4705-80b0-2a83f21c5d91

import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
import Definitions.Def_QEC_Locality_SeparatorProfile_Completion
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_edgeRegion_subset
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_localSharedBoundary_subset_ancestors
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
import Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_edgeRegion_subset
import Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_initialBoundary_incident_subset_ownerBoundary
import Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_localSharedBoundary_subset_ownerBoundary
import Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_ownerBoundary_card_le
import Theorems.Thm_QEC_Locality_edgeIncidentVertices_mono
import Theorems.Thm_QEC_Locality_mem_edgeDivisionSharedBoundary_iff
import Theorems.Thm_QEC_Locality_mem_edgeIncidentVertices_iff
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
private theorem EdgeRestrictedStoppedRecursion.refinedOwnerBoundary_card_le
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (owner : tree.refinedOwnerType beta exponent hProfile) :
    (tree.refinedOwnerBoundary beta exponent hProfile owner).card ≤
      6 * weightedSpineSeparatorBudget beta exponent r :=
  (tree.weightedRefinementAt beta exponent hProfile owner.1).ownerBoundary_card_le owner.2
private theorem EdgeRestrictedStoppedRecursion.refinedLocalSharedBoundary_subset_ownerBoundary
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (owner : tree.refinedOwnerType beta exponent hProfile) :
    edgeIncidentVertices (tree.refinedEdgeRegion beta exponent hProfile owner) ∩
        edgeDivisionSharedBoundary (tree.refinedEdgeRegion beta exponent hProfile)
          (tree.refinedEdgeActive beta exponent hProfile) ⊆
      tree.refinedOwnerBoundary beta exponent hProfile owner := by
  classical
  intro x hx
  have hxOwner : x ∈ edgeIncidentVertices
      (tree.refinedEdgeRegion beta exponent hProfile owner) :=
    (Finset.mem_inter.mp hx).1
  have hownerNonempty : (tree.refinedEdgeRegion beta exponent hProfile owner).Nonempty := by
    rcases (mem_edgeIncidentVertices_iff _ x).1 hxOwner with ⟨edge, hedge, _⟩
    exact ⟨edge, hedge⟩
  have hownerActive : owner ∈ tree.refinedEdgeActive beta exponent hProfile := by
    simp only [refinedEdgeActive, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hownerNonempty
  rcases (mem_edgeDivisionSharedBoundary_iff _ _ x).1 (Finset.mem_inter.mp hx).2 with
    ⟨i, hi, j, hj, hij, hxi, hxj⟩
  have hcandidate : ∃ candidate : tree.refinedOwnerType beta exponent hProfile,
      candidate ≠ owner ∧ candidate ∈ tree.refinedEdgeActive beta exponent hProfile ∧
        x ∈ edgeIncidentVertices (tree.refinedEdgeRegion beta exponent hProfile candidate) := by
    by_cases hiOwner : i = owner
    · refine ⟨j, ?_, hj, hxj⟩
      intro hjOwner
      exact hij (hiOwner.trans hjOwner.symm)
    · exact ⟨i, hiOwner, hi, hxi⟩
  rcases hcandidate with ⟨candidate, hne, hcandidateActive, hxCandidate⟩
  rcases owner with ⟨outer, inner⟩
  rcases candidate with ⟨candidateOuter, candidateInner⟩
  by_cases hsameOuter : candidateOuter = outer
  · subst candidateOuter
    have hinnerNe : candidateInner ≠ inner := by
      intro heq
      subst candidateInner
      exact hne rfl
    have hinnerActive : inner ∈
        (tree.weightedRefinementAt beta exponent hProfile outer).edgeActive := by
      simp only [WeightedBoundaryEdgeRecursion.edgeActive, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hownerNonempty
    have hcandidateInnerActive : candidateInner ∈
        (tree.weightedRefinementAt beta exponent hProfile outer).edgeActive := by
      have hnonempty := (@Finset.mem_filter _ _
        (fun _ => Finset.decidableNonempty) _ _).mp hcandidateActive
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hnonempty.2⟩
    have hxWeightedShared : x ∈ edgeDivisionSharedBoundary
        (tree.weightedRefinementAt beta exponent hProfile outer).edgeRegion
        (tree.weightedRefinementAt beta exponent hProfile outer).edgeActive :=
      (mem_edgeDivisionSharedBoundary_iff _ _ x).2
        ⟨inner, hinnerActive, candidateInner, hcandidateInnerActive, Ne.symm hinnerNe,
          hxOwner, hxCandidate⟩
    exact (tree.weightedRefinementAt beta exponent hProfile outer)
      |>.localSharedBoundary_subset_ownerBoundary inner
        (Finset.mem_inter.mpr ⟨hxOwner, hxWeightedShared⟩)
  · have hxOuter : x ∈ edgeIncidentVertices (tree.edgeRegion outer) := by
      exact (edgeIncidentVertices_mono
        ((tree.weightedRefinementAt beta exponent hProfile outer).edgeRegion_subset inner))
          hxOwner
    have hxCandidateOuter : x ∈ edgeIncidentVertices (tree.edgeRegion candidateOuter) := by
      exact (edgeIncidentVertices_mono
        ((tree.weightedRefinementAt beta exponent hProfile candidateOuter).edgeRegion_subset
          candidateInner)) hxCandidate
    have houterActive : outer ∈ tree.edgeActive := by
      simp only [EdgeRestrictedStoppedRecursion.edgeActive, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rcases (mem_edgeIncidentVertices_iff _ x).1 hxOuter with ⟨edge, hedge, _⟩
      exact ⟨edge, hedge⟩
    have hcandidateOuterActive : candidateOuter ∈ tree.edgeActive := by
      simp only [EdgeRestrictedStoppedRecursion.edgeActive, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rcases (mem_edgeIncidentVertices_iff _ x).1 hxCandidateOuter with
        ⟨edge, hedge, _⟩
      exact ⟨edge, hedge⟩
    have hxStoppedShared : x ∈ edgeDivisionSharedBoundary tree.edgeRegion tree.edgeActive :=
      (mem_edgeDivisionSharedBoundary_iff _ _ x).2
        ⟨outer, houterActive, candidateOuter, hcandidateOuterActive,
          Ne.symm hsameOuter, hxOuter, hxCandidateOuter⟩
    have hxAncestor : x ∈ tree.edgeOwnerAncestors outer :=
      tree.localSharedBoundary_subset_ancestors outer
        (Finset.mem_inter.mpr ⟨hxOuter, hxStoppedShared⟩)
    have hxTerminalBoundary : x ∈ tree.terminalBoundary outer :=
      Finset.mem_inter.mpr ⟨hxAncestor, hxOuter⟩
    exact (tree.weightedRefinementAt beta exponent hProfile outer)
      |>.initialBoundary_incident_subset_ownerBoundary inner
        (Finset.mem_inter.mpr ⟨hxTerminalBoundary, hxOwner⟩)
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
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (owner : tree.refinedOwnerType beta exponent hProfile) :
    (edgeIncidentVertices (tree.refinedEdgeRegion beta exponent hProfile owner) ∩
      edgeDivisionSharedBoundary (tree.refinedEdgeRegion beta exponent hProfile)
        (tree.refinedEdgeActive beta exponent hProfile)).card ≤
      6 * weightedSpineSeparatorBudget beta exponent r :=
  (Finset.card_le_card
    (tree.refinedLocalSharedBoundary_subset_ownerBoundary beta exponent hProfile owner)).trans
      (tree.refinedOwnerBoundary_card_le beta exponent hProfile owner)
end EdgeRestrictedStoppedRecursion
end QEC.Locality
