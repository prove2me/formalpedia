-- Prove2me | solution 1 for QEC.Locality.EdgeRestrictedStoppedRecursion.refinedEdgeRegions_isEdgeDivision
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:48:28.748489+00:00
-- url     : https://prove2.me/submissions/7f83a7e4-8f4b-4645-a59d-58b7549b7757

import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
import Definitions.Def_QEC_Locality_SeparatorProfile_Completion
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_edgeRegion_reverse
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_edgeRegion_subset
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_existsUnique_edgeOwner
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_edgeRegion_reverse
import Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_edgeRegion_subset
import Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_existsUnique_edgeOwner
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
private theorem EdgeRestrictedStoppedRecursion.refinedEdgeRegion_subset
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (owner : tree.refinedOwnerType beta exponent hProfile) :
    tree.refinedEdgeRegion beta exponent hProfile owner ⊆ edges :=
  ((tree.weightedRefinementAt beta exponent hProfile owner.1).edgeRegion_subset owner.2).trans
    (tree.edgeRegion_subset owner.1)
private theorem EdgeRestrictedStoppedRecursion.refinedEdgeRegion_reverse
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (owner : tree.refinedOwnerType beta exponent hProfile) (x y : ι) :
    (x, y) ∈ tree.refinedEdgeRegion beta exponent hProfile owner ↔
      (y, x) ∈ tree.refinedEdgeRegion beta exponent hProfile owner :=
  (tree.weightedRefinementAt beta exponent hProfile owner.1).edgeRegion_reverse owner.2 x y
private theorem EdgeRestrictedStoppedRecursion.existsUnique_refinedEdgeOwner
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (edge : ι × ι) (hedge : edge ∈ edges) :
    ∃! owner : tree.refinedOwnerType beta exponent hProfile,
      edge ∈ tree.refinedEdgeRegion beta exponent hProfile owner := by
  classical
  rcases tree.existsUnique_edgeOwner edge hedge with ⟨outer, houter, houterUnique⟩
  rcases (tree.weightedRefinementAt beta exponent hProfile outer).existsUnique_edgeOwner
      edge houter with ⟨inner, hinner, hinnerUnique⟩
  refine ⟨⟨outer, inner⟩, hinner, ?_⟩
  intro candidate hcandidate
  have hcandOuter : edge ∈ tree.edgeRegion candidate.1 :=
    (tree.weightedRefinementAt beta exponent hProfile candidate.1).edgeRegion_subset
      candidate.2 hcandidate
  have houterEq : candidate.1 = outer := houterUnique candidate.1 hcandOuter
  rcases candidate with ⟨candidateOuter, candidateInner⟩
  dsimp at houterEq
  subst candidateOuter
  have hinnerEq : candidateInner = inner := hinnerUnique candidateInner hcandidate
  subst candidateInner
  rfl
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
    (hroot : edges = directedEdgeFinset G) :
    IsEdgeDivision G (tree.refinedEdgeRegion beta exponent hProfile)
      (tree.refinedEdgeActive beta exponent hProfile) := by
  refine ⟨?_, ?_, ?_⟩
  · intro owner _ edge hedge
    rw [← hroot]
    exact tree.refinedEdgeRegion_subset beta exponent hProfile owner hedge
  · intro owner _ x y
    exact tree.refinedEdgeRegion_reverse beta exponent hProfile owner x y
  · intro edge hedge
    have hedgeRoot : edge ∈ edges := by simpa [hroot] using hedge
    rcases tree.existsUnique_refinedEdgeOwner beta exponent hProfile edge hedgeRoot with
      ⟨owner, howner, hunique⟩
    refine ⟨owner, ⟨?_, howner⟩, ?_⟩
    · simp only [refinedEdgeActive, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨edge, howner⟩
    · intro candidate hcandidate
      exact hunique candidate hcandidate.2
end EdgeRestrictedStoppedRecursion
end QEC.Locality
