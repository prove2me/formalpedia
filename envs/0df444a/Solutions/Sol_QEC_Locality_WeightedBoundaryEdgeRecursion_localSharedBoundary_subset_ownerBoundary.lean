-- Prove2me | solution 1 for QEC.Locality.WeightedBoundaryEdgeRecursion.localSharedBoundary_subset_ownerBoundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:48:27.896797+00:00
-- url     : https://prove2.me/submissions/d7925e13-a594-499a-9b89-821ecc2964af

import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
import Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_edgeRegion_subset
import Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_initialBoundary_incident_subset_ownerBoundary
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_edgeRegion_subset
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_disjoint_stopSides
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_stopSides_disjoint
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
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
private theorem childCarriers_inter_subset_separator
    {first second separator : Finset ι} (hdisjoint : Disjoint first second) :
    (weightedSpineChildCarrier first separator) ∩
        (weightedSpineChildCarrier second separator) ⊆ separator := by
  intro x hx
  rcases Finset.mem_inter.mp hx with ⟨hxFirstCarrier, hxSecondCarrier⟩
  rcases Finset.mem_union.mp hxFirstCarrier with hxFirst | hxSeparator
  · rcases Finset.mem_union.mp hxSecondCarrier with hxSecond | hxSeparator
    · exact False.elim ((Finset.disjoint_left.mp hdisjoint) hxFirst hxSecond)
    · exact hxSeparator
  · exact hxSeparator
private theorem weighted_first_second_terminal_inter_subset_separator
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (spine : MarkedSeparatorSpine (edgeRestrictedGraph G edges) boundary vertices)
    (firstTree : WeightedBoundaryEdgeRecursion G r spineBudget
      (weightedSpineFirstEdges edges spine.exposedSide)
      (weightedSpineChildCarrier spine.exposedSide (markedSpineSeparatorUnion spine))
      (weightedSpineChildBoundary boundary spine.exposedSide
        (markedSpineSeparatorUnion spine)))
    (secondTree : WeightedBoundaryEdgeRecursion G r spineBudget
      (weightedSpineSecondEdges edges spine.exposedSide spine.stopSides.1)
      (weightedSpineChildCarrier spine.stopSides.1 (markedSpineSeparatorUnion spine))
      (weightedSpineChildBoundary boundary spine.stopSides.1
        (markedSpineSeparatorUnion spine)))
    (firstOwner : firstTree.edgeOwnerType) (secondOwner : secondTree.edgeOwnerType) :
    edgeIncidentVertices (firstTree.edgeRegion firstOwner) ∩
        edgeIncidentVertices (secondTree.edgeRegion secondOwner) ⊆
      markedSpineSeparatorUnion spine := by
  apply (Finset.inter_subset_inter
    (weighted_first_terminal_incident_subset hsubset hincident spine firstTree firstOwner)
    (weighted_second_terminal_incident_subset hsubset hincident spine secondTree secondOwner)).trans
  exact childCarriers_inter_subset_separator spine.exposedSide_disjoint_stopSides.1
private theorem weighted_first_third_terminal_inter_subset_separator
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (spine : MarkedSeparatorSpine (edgeRestrictedGraph G edges) boundary vertices)
    (firstTree : WeightedBoundaryEdgeRecursion G r spineBudget
      (weightedSpineFirstEdges edges spine.exposedSide)
      (weightedSpineChildCarrier spine.exposedSide (markedSpineSeparatorUnion spine))
      (weightedSpineChildBoundary boundary spine.exposedSide
        (markedSpineSeparatorUnion spine)))
    (thirdTree : WeightedBoundaryEdgeRecursion G r spineBudget
      (weightedSpineThirdEdges edges spine.exposedSide spine.stopSides.1)
      (weightedSpineChildCarrier spine.stopSides.2 (markedSpineSeparatorUnion spine))
      (weightedSpineChildBoundary boundary spine.stopSides.2
        (markedSpineSeparatorUnion spine)))
    (firstOwner : firstTree.edgeOwnerType) (thirdOwner : thirdTree.edgeOwnerType) :
    edgeIncidentVertices (firstTree.edgeRegion firstOwner) ∩
        edgeIncidentVertices (thirdTree.edgeRegion thirdOwner) ⊆
      markedSpineSeparatorUnion spine := by
  apply (Finset.inter_subset_inter
    (weighted_first_terminal_incident_subset hsubset hincident spine firstTree firstOwner)
    (weighted_third_terminal_incident_subset hincident spine thirdTree thirdOwner)).trans
  exact childCarriers_inter_subset_separator spine.exposedSide_disjoint_stopSides.2
private theorem weighted_second_third_terminal_inter_subset_separator
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (spine : MarkedSeparatorSpine (edgeRestrictedGraph G edges) boundary vertices)
    (secondTree : WeightedBoundaryEdgeRecursion G r spineBudget
      (weightedSpineSecondEdges edges spine.exposedSide spine.stopSides.1)
      (weightedSpineChildCarrier spine.stopSides.1 (markedSpineSeparatorUnion spine))
      (weightedSpineChildBoundary boundary spine.stopSides.1
        (markedSpineSeparatorUnion spine)))
    (thirdTree : WeightedBoundaryEdgeRecursion G r spineBudget
      (weightedSpineThirdEdges edges spine.exposedSide spine.stopSides.1)
      (weightedSpineChildCarrier spine.stopSides.2 (markedSpineSeparatorUnion spine))
      (weightedSpineChildBoundary boundary spine.stopSides.2
        (markedSpineSeparatorUnion spine)))
    (secondOwner : secondTree.edgeOwnerType) (thirdOwner : thirdTree.edgeOwnerType) :
    edgeIncidentVertices (secondTree.edgeRegion secondOwner) ∩
        edgeIncidentVertices (thirdTree.edgeRegion thirdOwner) ⊆
      markedSpineSeparatorUnion spine := by
  apply (Finset.inter_subset_inter
    (weighted_second_terminal_incident_subset hsubset hincident spine secondTree secondOwner)
    (weighted_third_terminal_incident_subset hincident spine thirdTree thirdOwner)).trans
  exact childCarriers_inter_subset_separator spine.stopSides_disjoint
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
    edgeIncidentVertices (tree.edgeRegion owner) ∩
        edgeDivisionSharedBoundary tree.edgeRegion tree.edgeActive ⊆
      tree.ownerBoundary owner := by
  classical
  induction tree with
  | leaf _ _ _ _ _ _ =>
      intro x hx
      rcases (mem_edgeDivisionSharedBoundary_iff _ _ x).1 (Finset.mem_inter.mp hx).2 with
        ⟨i, hi, j, hj, hij, hxi, hxj⟩
      have : i = j := by
        simpa [edgeOwnerType] using (Subsingleton.elim (α := Unit) i j)
      exact False.elim (hij this)
  | @split edges vertices boundary hsubset hsymmetric hincident hboundary hcard spine
      hseparatorCard hboundaryLarge
      firstTree secondTree thirdTree ihFirst ihSecond ihThird =>
      let root := WeightedBoundaryEdgeRecursion.split hsubset hsymmetric hincident hboundary hcard
        spine hseparatorCard hboundaryLarge firstTree secondTree thirdTree
      cases owner with
      | inl owner =>
          intro x hx
          have hxOwner : x ∈ edgeIncidentVertices (firstTree.edgeRegion owner) := by
            simpa [root, edgeRegion] using (Finset.mem_inter.mp hx).1
          have hownerActive : owner ∈ firstTree.edgeActive := by
            simp only [edgeActive, Finset.mem_filter, Finset.mem_univ, true_and]
            rcases (mem_edgeIncidentVertices_iff _ x).1 hxOwner with ⟨edge, hedge, _⟩
            exact ⟨edge, hedge⟩
          rcases (mem_edgeDivisionSharedBoundary_iff _ _ x).1
              (Finset.mem_inter.mp hx).2 with ⟨i, hi, j, hj, hij, hxi, hxj⟩
          have hcandidate : ∃ candidate : root.edgeOwnerType,
              candidate ≠ Sum.inl owner ∧ candidate ∈ root.edgeActive ∧
                x ∈ edgeIncidentVertices (root.edgeRegion candidate) := by
            by_cases hiOwner : i = Sum.inl owner
            · refine ⟨j, ?_, hj, hxj⟩
              intro hjOwner
              exact hij (hiOwner.trans hjOwner.symm)
            · exact ⟨i, hiOwner, hi, hxi⟩
          rcases hcandidate with ⟨candidate, hne, hcandActive, hxcandidate⟩
          cases candidate with
          | inl candidate =>
              have hcandidateActive : candidate ∈ firstTree.edgeActive := by
                have hnonempty := (@Finset.mem_filter _ _
                  (fun _ => Finset.decidableNonempty) _ _).mp hcandActive
                apply Finset.mem_filter.mpr
                exact ⟨Finset.mem_univ _, hnonempty.2⟩
              have hxcandidate' : x ∈ edgeIncidentVertices (firstTree.edgeRegion candidate) := by
                simpa [root, edgeRegion] using hxcandidate
              have hxShared : x ∈ edgeDivisionSharedBoundary
                  firstTree.edgeRegion firstTree.edgeActive := by
                apply (mem_edgeDivisionSharedBoundary_iff _ _ x).2
                refine ⟨owner, hownerActive, candidate, hcandidateActive, ?_, hxOwner,
                  hxcandidate'⟩
                intro heq
                exact hne (congrArg Sum.inl heq.symm)
              simpa [root, ownerBoundary] using
                (ihFirst owner (Finset.mem_inter.mpr ⟨hxOwner, hxShared⟩))
          | inr candidate =>
              cases candidate with
              | inl candidate =>
                  have hxcandidate' : x ∈ edgeIncidentVertices
                      (secondTree.edgeRegion candidate) := by
                    simpa [root, edgeRegion] using hxcandidate
                  have hxSeparator : x ∈ markedSpineSeparatorUnion spine :=
                    weighted_first_second_terminal_inter_subset_separator hsubset hincident spine
                      firstTree secondTree owner candidate
                      (Finset.mem_inter.mpr ⟨hxOwner, hxcandidate'⟩)
                  have hxChildBoundary : x ∈ weightedSpineChildBoundary boundary
                      spine.exposedSide (markedSpineSeparatorUnion spine) :=
                    Finset.mem_union_left _ hxSeparator
                  simpa [root, ownerBoundary] using
                    (firstTree.initialBoundary_incident_subset_ownerBoundary owner
                      (Finset.mem_inter.mpr ⟨hxChildBoundary, hxOwner⟩))
              | inr candidate =>
                  have hxcandidate' : x ∈ edgeIncidentVertices
                      (thirdTree.edgeRegion candidate) := by
                    simpa [root, edgeRegion] using hxcandidate
                  have hxSeparator : x ∈ markedSpineSeparatorUnion spine :=
                    weighted_first_third_terminal_inter_subset_separator hsubset hincident spine
                      firstTree thirdTree owner candidate
                      (Finset.mem_inter.mpr ⟨hxOwner, hxcandidate'⟩)
                  have hxChildBoundary : x ∈ weightedSpineChildBoundary boundary
                      spine.exposedSide (markedSpineSeparatorUnion spine) :=
                    Finset.mem_union_left _ hxSeparator
                  simpa [root, ownerBoundary] using
                    (firstTree.initialBoundary_incident_subset_ownerBoundary owner
                      (Finset.mem_inter.mpr ⟨hxChildBoundary, hxOwner⟩))
      | inr owner =>
          cases owner with
          | inl owner =>
              intro x hx
              have hxOwner : x ∈ edgeIncidentVertices (secondTree.edgeRegion owner) := by
                simpa [root, edgeRegion] using (Finset.mem_inter.mp hx).1
              have hownerActive : owner ∈ secondTree.edgeActive := by
                simp only [edgeActive, Finset.mem_filter, Finset.mem_univ, true_and]
                rcases (mem_edgeIncidentVertices_iff _ x).1 hxOwner with ⟨edge, hedge, _⟩
                exact ⟨edge, hedge⟩
              rcases (mem_edgeDivisionSharedBoundary_iff _ _ x).1
                  (Finset.mem_inter.mp hx).2 with ⟨i, hi, j, hj, hij, hxi, hxj⟩
              have hcandidate : ∃ candidate : root.edgeOwnerType,
                  candidate ≠ Sum.inr (Sum.inl owner) ∧ candidate ∈ root.edgeActive ∧
                    x ∈ edgeIncidentVertices (root.edgeRegion candidate) := by
                by_cases hiOwner : i = Sum.inr (Sum.inl owner)
                · refine ⟨j, ?_, hj, hxj⟩
                  intro hjOwner
                  exact hij (hiOwner.trans hjOwner.symm)
                · exact ⟨i, hiOwner, hi, hxi⟩
              rcases hcandidate with ⟨candidate, hne, hcandActive, hxcandidate⟩
              cases candidate with
              | inl candidate =>
                  have hxcandidate' : x ∈ edgeIncidentVertices
                      (firstTree.edgeRegion candidate) := by
                    simpa [root, edgeRegion] using hxcandidate
                  have hxSeparator : x ∈ markedSpineSeparatorUnion spine :=
                    weighted_first_second_terminal_inter_subset_separator hsubset hincident spine
                      firstTree secondTree candidate owner
                      (Finset.mem_inter.mpr ⟨hxcandidate', hxOwner⟩)
                  have hxChildBoundary : x ∈ weightedSpineChildBoundary boundary
                      spine.stopSides.1 (markedSpineSeparatorUnion spine) :=
                    Finset.mem_union_left _ hxSeparator
                  simpa [root, ownerBoundary] using
                    (secondTree.initialBoundary_incident_subset_ownerBoundary owner
                      (Finset.mem_inter.mpr ⟨hxChildBoundary, hxOwner⟩))
              | inr candidate =>
                  cases candidate with
                  | inl candidate =>
                      have hcandidateActive : candidate ∈ secondTree.edgeActive := by
                        have hnonempty := (@Finset.mem_filter _ _
                          (fun _ => Finset.decidableNonempty) _ _).mp hcandActive
                        apply Finset.mem_filter.mpr
                        exact ⟨Finset.mem_univ _, hnonempty.2⟩
                      have hxcandidate' : x ∈ edgeIncidentVertices
                          (secondTree.edgeRegion candidate) := by
                        simpa [root, edgeRegion] using hxcandidate
                      have hxShared : x ∈ edgeDivisionSharedBoundary
                          secondTree.edgeRegion secondTree.edgeActive := by
                        apply (mem_edgeDivisionSharedBoundary_iff _ _ x).2
                        refine ⟨owner, hownerActive, candidate, hcandidateActive, ?_, hxOwner,
                          hxcandidate'⟩
                        intro heq
                        exact hne (congrArg (fun z => Sum.inr (Sum.inl z)) heq.symm)
                      simpa [root, ownerBoundary] using
                        (ihSecond owner (Finset.mem_inter.mpr ⟨hxOwner, hxShared⟩))
                  | inr candidate =>
                      have hxcandidate' : x ∈ edgeIncidentVertices
                          (thirdTree.edgeRegion candidate) := by
                        simpa [root, edgeRegion] using hxcandidate
                      have hxSeparator : x ∈ markedSpineSeparatorUnion spine :=
                        weighted_second_third_terminal_inter_subset_separator hsubset hincident
                          spine secondTree thirdTree owner candidate
                          (Finset.mem_inter.mpr ⟨hxOwner, hxcandidate'⟩)
                      have hxChildBoundary : x ∈ weightedSpineChildBoundary boundary
                          spine.stopSides.1 (markedSpineSeparatorUnion spine) :=
                        Finset.mem_union_left _ hxSeparator
                      simpa [root, ownerBoundary] using
                        (secondTree.initialBoundary_incident_subset_ownerBoundary owner
                          (Finset.mem_inter.mpr ⟨hxChildBoundary, hxOwner⟩))
          | inr owner =>
              intro x hx
              have hxOwner : x ∈ edgeIncidentVertices (thirdTree.edgeRegion owner) := by
                simpa [root, edgeRegion] using (Finset.mem_inter.mp hx).1
              have hownerActive : owner ∈ thirdTree.edgeActive := by
                simp only [edgeActive, Finset.mem_filter, Finset.mem_univ, true_and]
                rcases (mem_edgeIncidentVertices_iff _ x).1 hxOwner with ⟨edge, hedge, _⟩
                exact ⟨edge, hedge⟩
              rcases (mem_edgeDivisionSharedBoundary_iff _ _ x).1
                  (Finset.mem_inter.mp hx).2 with ⟨i, hi, j, hj, hij, hxi, hxj⟩
              have hcandidate : ∃ candidate : root.edgeOwnerType,
                  candidate ≠ Sum.inr (Sum.inr owner) ∧ candidate ∈ root.edgeActive ∧
                    x ∈ edgeIncidentVertices (root.edgeRegion candidate) := by
                by_cases hiOwner : i = Sum.inr (Sum.inr owner)
                · refine ⟨j, ?_, hj, hxj⟩
                  intro hjOwner
                  exact hij (hiOwner.trans hjOwner.symm)
                · exact ⟨i, hiOwner, hi, hxi⟩
              rcases hcandidate with ⟨candidate, hne, hcandActive, hxcandidate⟩
              cases candidate with
              | inl candidate =>
                  have hxcandidate' : x ∈ edgeIncidentVertices
                      (firstTree.edgeRegion candidate) := by
                    simpa [root, edgeRegion] using hxcandidate
                  have hxSeparator : x ∈ markedSpineSeparatorUnion spine :=
                    weighted_first_third_terminal_inter_subset_separator hsubset hincident spine
                      firstTree thirdTree candidate owner
                      (Finset.mem_inter.mpr ⟨hxcandidate', hxOwner⟩)
                  have hxChildBoundary : x ∈ weightedSpineChildBoundary boundary
                      spine.stopSides.2 (markedSpineSeparatorUnion spine) :=
                    Finset.mem_union_left _ hxSeparator
                  simpa [root, ownerBoundary] using
                    (thirdTree.initialBoundary_incident_subset_ownerBoundary owner
                      (Finset.mem_inter.mpr ⟨hxChildBoundary, hxOwner⟩))
              | inr candidate =>
                  cases candidate with
                  | inl candidate =>
                      have hxcandidate' : x ∈ edgeIncidentVertices
                          (secondTree.edgeRegion candidate) := by
                        simpa [root, edgeRegion] using hxcandidate
                      have hxSeparator : x ∈ markedSpineSeparatorUnion spine :=
                        weighted_second_third_terminal_inter_subset_separator hsubset hincident
                          spine secondTree thirdTree candidate owner
                          (Finset.mem_inter.mpr ⟨hxcandidate', hxOwner⟩)
                      have hxChildBoundary : x ∈ weightedSpineChildBoundary boundary
                          spine.stopSides.2 (markedSpineSeparatorUnion spine) :=
                        Finset.mem_union_left _ hxSeparator
                      simpa [root, ownerBoundary] using
                        (thirdTree.initialBoundary_incident_subset_ownerBoundary owner
                          (Finset.mem_inter.mpr ⟨hxChildBoundary, hxOwner⟩))
                  | inr candidate =>
                      have hcandidateActive : candidate ∈ thirdTree.edgeActive := by
                        have hnonempty := (@Finset.mem_filter _ _
                          (fun _ => Finset.decidableNonempty) _ _).mp hcandActive
                        apply Finset.mem_filter.mpr
                        exact ⟨Finset.mem_univ _, hnonempty.2⟩
                      have hxcandidate' : x ∈ edgeIncidentVertices
                          (thirdTree.edgeRegion candidate) := by
                        simpa [root, edgeRegion] using hxcandidate
                      have hxShared : x ∈ edgeDivisionSharedBoundary
                          thirdTree.edgeRegion thirdTree.edgeActive := by
                        apply (mem_edgeDivisionSharedBoundary_iff _ _ x).2
                        refine ⟨owner, hownerActive, candidate, hcandidateActive, ?_, hxOwner,
                          hxcandidate'⟩
                        intro heq
                        exact hne (congrArg (fun z => Sum.inr (Sum.inr z)) heq.symm)
                      simpa [root, ownerBoundary] using
                        (ihThird owner (Finset.mem_inter.mpr ⟨hxOwner, hxShared⟩))
end WeightedBoundaryEdgeRecursion
end QEC.Locality
