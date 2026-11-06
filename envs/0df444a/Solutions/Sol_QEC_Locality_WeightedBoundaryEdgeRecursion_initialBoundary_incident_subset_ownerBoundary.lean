-- Prove2me | solution 1 for QEC.Locality.WeightedBoundaryEdgeRecursion.initialBoundary_incident_subset_ownerBoundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:45:27.215085+00:00
-- url     : https://prove2.me/submissions/a8e4d767-19d4-43c8-aff3-2fad7b6b3abc

import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
import Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_edgeRegion_subset
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_edgeRegion_subset
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_edgeIncidentVertices_mono
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
private theorem weighted_first_terminal_incident_subset
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (spine : MarkedSeparatorSpine (edgeRestrictedGraph G edges) boundary vertices)
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget
      (weightedSpineFirstEdges edges spine.exposedSide)
      (weightedSpineChildCarrier spine.exposedSide (markedSpineSeparatorUnion spine))
      (weightedSpineChildBoundary boundary spine.exposedSide
        (markedSpineSeparatorUnion spine)))
    (owner : tree.edgeOwnerType) :
    edgeIncidentVertices (tree.edgeRegion owner) ⊆
      weightedSpineChildCarrier spine.exposedSide (markedSpineSeparatorUnion spine) := by
  apply (edgeIncidentVertices_mono (tree.edgeRegion_subset owner)).trans
  exact weightedSpineFirstEdges_incident_subset G hsubset hincident spine
private theorem weighted_second_terminal_incident_subset
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (spine : MarkedSeparatorSpine (edgeRestrictedGraph G edges) boundary vertices)
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget
      (weightedSpineSecondEdges edges spine.exposedSide spine.stopSides.1)
      (weightedSpineChildCarrier spine.stopSides.1 (markedSpineSeparatorUnion spine))
      (weightedSpineChildBoundary boundary spine.stopSides.1
        (markedSpineSeparatorUnion spine)))
    (owner : tree.edgeOwnerType) :
    edgeIncidentVertices (tree.edgeRegion owner) ⊆
      weightedSpineChildCarrier spine.stopSides.1 (markedSpineSeparatorUnion spine) := by
  apply (edgeIncidentVertices_mono (tree.edgeRegion_subset owner)).trans
  exact weightedSpineSecondEdges_incident_subset G hsubset hincident spine
private theorem weighted_third_terminal_incident_subset
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (spine : MarkedSeparatorSpine (edgeRestrictedGraph G edges) boundary vertices)
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget
      (weightedSpineThirdEdges edges spine.exposedSide spine.stopSides.1)
      (weightedSpineChildCarrier spine.stopSides.2 (markedSpineSeparatorUnion spine))
      (weightedSpineChildBoundary boundary spine.stopSides.2
        (markedSpineSeparatorUnion spine)))
    (owner : tree.edgeOwnerType) :
    edgeIncidentVertices (tree.edgeRegion owner) ⊆
      weightedSpineChildCarrier spine.stopSides.2 (markedSpineSeparatorUnion spine) := by
  apply (edgeIncidentVertices_mono (tree.edgeRegion_subset owner)).trans
  exact weightedSpineThirdEdges_incident_subset G hincident spine
end QEC.Locality
end

set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
namespace WeightedBoundaryEdgeRecursion
theorem _root_.solution
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary)
    (owner : tree.edgeOwnerType) :
    boundary ∩ edgeIncidentVertices (tree.edgeRegion owner) ⊆ tree.ownerBoundary owner := by
  induction tree with
  | leaf _ _ _ _ _ _ =>
      intro x hx
      simpa [ownerBoundary] using (Finset.mem_inter.mp hx).1
  | @split edges vertices boundary hsubset hsymmetric hincident hboundary hcard spine
      hseparatorCard hboundaryLarge
      firstTree secondTree thirdTree ihFirst ihSecond ihThird =>
      cases owner with
      | inl owner =>
          intro x hx
          have hxInitial := (Finset.mem_inter.mp hx).1
          have hxIncident : x ∈ edgeIncidentVertices (firstTree.edgeRegion owner) := by
            simpa [edgeRegion] using (Finset.mem_inter.mp hx).2
          have hxCarrier := weighted_first_terminal_incident_subset hsubset hincident spine
            firstTree owner hxIncident
          have hxChildBoundary : x ∈ weightedSpineChildBoundary boundary spine.exposedSide
              (markedSpineSeparatorUnion spine) :=
            Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxInitial, hxCarrier⟩)
          simpa [ownerBoundary] using
            (ihFirst owner (Finset.mem_inter.mpr ⟨hxChildBoundary, hxIncident⟩))
      | inr owner =>
          cases owner with
          | inl owner =>
              intro x hx
              have hxInitial := (Finset.mem_inter.mp hx).1
              have hxIncident : x ∈ edgeIncidentVertices (secondTree.edgeRegion owner) := by
                simpa [edgeRegion] using (Finset.mem_inter.mp hx).2
              have hxCarrier := weighted_second_terminal_incident_subset hsubset hincident spine
                secondTree owner hxIncident
              have hxChildBoundary : x ∈ weightedSpineChildBoundary boundary spine.stopSides.1
                  (markedSpineSeparatorUnion spine) :=
                Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxInitial, hxCarrier⟩)
              simpa [ownerBoundary] using
                (ihSecond owner (Finset.mem_inter.mpr ⟨hxChildBoundary, hxIncident⟩))
          | inr owner =>
              intro x hx
              have hxInitial := (Finset.mem_inter.mp hx).1
              have hxIncident : x ∈ edgeIncidentVertices (thirdTree.edgeRegion owner) := by
                simpa [edgeRegion] using (Finset.mem_inter.mp hx).2
              have hxCarrier := weighted_third_terminal_incident_subset hincident spine
                thirdTree owner hxIncident
              have hxChildBoundary : x ∈ weightedSpineChildBoundary boundary spine.stopSides.2
                  (markedSpineSeparatorUnion spine) :=
                Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxInitial, hxCarrier⟩)
              simpa [ownerBoundary] using
                (ihThird owner (Finset.mem_inter.mpr ⟨hxChildBoundary, hxIncident⟩))
end WeightedBoundaryEdgeRecursion
end QEC.Locality
