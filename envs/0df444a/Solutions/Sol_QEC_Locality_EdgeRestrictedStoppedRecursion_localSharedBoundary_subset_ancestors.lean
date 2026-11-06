-- Prove2me | solution 1 for QEC.Locality.EdgeRestrictedStoppedRecursion.localSharedBoundary_subset_ancestors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:30:38.583033+00:00
-- url     : https://prove2.me/submissions/93d508fc-382d-4348-95f8-df14d454bb8c

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
import Theorems.Thm_QEC_Locality_separatorLeftEdges_incident_subset
import Theorems.Thm_QEC_Locality_separatorRightEdges_incident_subset
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_edgeRegion_subset
import Theorems.Thm_QEC_Locality_edgeIncidentVertices_mono
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
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
private theorem left_terminal_incident_subset
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)}
    {vertices left separator right : Finset ι}
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hsymmetric : ReverseSymmetricEdgeSet edges)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (hpartition :
      TwoThirdsBalancedPartitionAfterDeleting (edgeRestrictedGraph G edges)
        vertices left separator right)
    (leftTree : EdgeRestrictedStoppedRecursion G r
      (separatorLeftEdges edges left) (left ∪ separator))
    (owner : leftTree.edgeOwnerType) :
    edgeIncidentVertices (leftTree.edgeRegion owner) ⊆ left ∪ separator := by
  apply (edgeIncidentVertices_mono (leftTree.edgeRegion_subset owner)).trans
  exact separatorLeftEdges_incident_subset G edges vertices left separator right
    hsubset hsymmetric hincident hpartition
private theorem right_terminal_incident_subset
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)}
    {vertices left separator right : Finset ι}
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hsymmetric : ReverseSymmetricEdgeSet edges)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (hpartition :
      TwoThirdsBalancedPartitionAfterDeleting (edgeRestrictedGraph G edges)
        vertices left separator right)
    (rightTree : EdgeRestrictedStoppedRecursion G r
      (separatorRightEdges edges left) (right ∪ separator))
    (owner : rightTree.edgeOwnerType) :
    edgeIncidentVertices (rightTree.edgeRegion owner) ⊆ right ∪ separator := by
  apply (edgeIncidentVertices_mono (rightTree.edgeRegion_subset owner)).trans
  exact separatorRightEdges_incident_subset G edges vertices left separator right
    hsubset hsymmetric hincident hpartition
private theorem cross_terminal_incident_inter_subset_separator
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)}
    {vertices left separator right : Finset ι}
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hsymmetric : ReverseSymmetricEdgeSet edges)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (hpartition :
      TwoThirdsBalancedPartitionAfterDeleting (edgeRestrictedGraph G edges)
        vertices left separator right)
    (leftTree : EdgeRestrictedStoppedRecursion G r
      (separatorLeftEdges edges left) (left ∪ separator))
    (rightTree : EdgeRestrictedStoppedRecursion G r
      (separatorRightEdges edges left) (right ∪ separator))
    (leftOwner : leftTree.edgeOwnerType) (rightOwner : rightTree.edgeOwnerType) :
    edgeIncidentVertices (leftTree.edgeRegion leftOwner) ∩
      edgeIncidentVertices (rightTree.edgeRegion rightOwner) ⊆ separator := by
  intro x hx
  rcases Finset.mem_inter.mp hx with ⟨hxleft, hxright⟩
  by_contra hxseparator
  have hxleft' := left_terminal_incident_subset hsubset hsymmetric hincident hpartition
    leftTree leftOwner hxleft
  have hxright' := right_terminal_incident_subset hsubset hsymmetric hincident hpartition
    rightTree rightOwner hxright
  have hxL : x ∈ left := by
    rcases Finset.mem_union.mp hxleft' with hxL | hxS
    · exact hxL
    · exact False.elim (hxseparator hxS)
  have hxR : x ∈ right := by
    rcases Finset.mem_union.mp hxright' with hxR | hxS
    · exact hxR
    · exact False.elim (hxseparator hxS)
  exact (Finset.disjoint_left.mp hpartition.2.2.1) hxL hxR
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
    (owner : tree.edgeOwnerType) :
    (edgeIncidentVertices (tree.edgeRegion owner)) ∩
      edgeDivisionSharedBoundary tree.edgeRegion tree.edgeActive ⊆
        tree.edgeOwnerAncestors owner := by
  classical
  induction tree with
  | leaf hsubset hsymmetric hincident hcard =>
      intro x hx
      rcases (mem_edgeDivisionSharedBoundary_iff _ _ x).1 (Finset.mem_inter.mp hx).2 with
        ⟨i, hi, j, hj, hij, hxi, hxj⟩
      have heq : i = j := by
        simpa [edgeOwnerType] using (Subsingleton.elim (α := Unit) i j)
      exact False.elim (hij heq)
  | @split edges vertices left separator right hsubset hsymmetric hincident
      hpartition hminimum hleft hright leftTree rightTree ihLeft ihRight =>
      cases owner with
      | inl owner =>
          intro x hx
          have hxOwner : x ∈ edgeIncidentVertices (leftTree.edgeRegion owner) := by
            simpa [edgeRegion] using (Finset.mem_inter.mp hx).1
          have hownerNonempty : (leftTree.edgeRegion owner).Nonempty := by
            rcases (mem_edgeIncidentVertices_iff _ x).1 hxOwner with ⟨edge, hedge, _⟩
            exact ⟨edge, hedge⟩
          have hownerActive : owner ∈ leftTree.edgeActive := by
            simp only [edgeActive, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hownerNonempty
          rcases (mem_edgeDivisionSharedBoundary_iff _ _ x).1 (Finset.mem_inter.mp hx).2 with
            ⟨i, hi, j, hj, hij, hxi, hxj⟩
          have hcandidate : ∃ candidate : Sum leftTree.edgeOwnerType rightTree.edgeOwnerType,
              candidate ≠ Sum.inl owner ∧ candidate ∈
                (EdgeRestrictedStoppedRecursion.split hsubset hsymmetric hincident
                  hpartition hminimum hleft hright leftTree rightTree).edgeActive ∧
              x ∈ edgeIncidentVertices
                ((EdgeRestrictedStoppedRecursion.split hsubset hsymmetric hincident
                  hpartition hminimum hleft hright leftTree rightTree).edgeRegion candidate) := by
            by_cases hiOwner : i = Sum.inl owner
            · refine ⟨j, ?_, hj, hxj⟩
              intro hjOwner
              apply hij
              exact hiOwner.trans hjOwner.symm
            · exact ⟨i, hiOwner, hi, hxi⟩
          rcases hcandidate with ⟨candidate, hne, hcandActive, hxcandidate⟩
          cases candidate with
          | inl candidate =>
              have hcandidateActive : candidate ∈ leftTree.edgeActive := by
                have hnonempty := (@Finset.mem_filter _ _
                  (fun _ => Finset.decidableNonempty) _ _).mp hcandActive
                apply Finset.mem_filter.mpr
                exact ⟨Finset.mem_univ _, hnonempty.2⟩
              have hxcandidate' : x ∈ edgeIncidentVertices (leftTree.edgeRegion candidate) := by
                simpa [edgeRegion] using hxcandidate
              have hxChildShared : x ∈ edgeDivisionSharedBoundary
                  leftTree.edgeRegion leftTree.edgeActive := by
                apply (mem_edgeDivisionSharedBoundary_iff _ _ x).2
                refine ⟨owner, hownerActive, candidate, hcandidateActive, ?_, hxOwner,
                  hxcandidate'⟩
                intro heq
                exact hne (congrArg Sum.inl heq.symm)
              exact Finset.mem_union_right _
                (ihLeft owner (Finset.mem_inter.mpr ⟨hxOwner, hxChildShared⟩))
          | inr candidate =>
              have hxcandidate' : x ∈ edgeIncidentVertices (rightTree.edgeRegion candidate) := by
                simpa [edgeRegion] using hxcandidate
              exact Finset.mem_union_left _
                (cross_terminal_incident_inter_subset_separator hsubset hsymmetric hincident
                  hpartition leftTree rightTree owner candidate
                  (Finset.mem_inter.mpr ⟨hxOwner, hxcandidate'⟩))
      | inr owner =>
          intro x hx
          have hxOwner : x ∈ edgeIncidentVertices (rightTree.edgeRegion owner) := by
            simpa [edgeRegion] using (Finset.mem_inter.mp hx).1
          have hownerNonempty : (rightTree.edgeRegion owner).Nonempty := by
            rcases (mem_edgeIncidentVertices_iff _ x).1 hxOwner with ⟨edge, hedge, _⟩
            exact ⟨edge, hedge⟩
          have hownerActive : owner ∈ rightTree.edgeActive := by
            simp only [edgeActive, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hownerNonempty
          rcases (mem_edgeDivisionSharedBoundary_iff _ _ x).1 (Finset.mem_inter.mp hx).2 with
            ⟨i, hi, j, hj, hij, hxi, hxj⟩
          have hcandidate : ∃ candidate : Sum leftTree.edgeOwnerType rightTree.edgeOwnerType,
              candidate ≠ Sum.inr owner ∧ candidate ∈
                (EdgeRestrictedStoppedRecursion.split hsubset hsymmetric hincident
                  hpartition hminimum hleft hright leftTree rightTree).edgeActive ∧
              x ∈ edgeIncidentVertices
                ((EdgeRestrictedStoppedRecursion.split hsubset hsymmetric hincident
                  hpartition hminimum hleft hright leftTree rightTree).edgeRegion candidate) := by
            by_cases hiOwner : i = Sum.inr owner
            · refine ⟨j, ?_, hj, hxj⟩
              intro hjOwner
              apply hij
              exact hiOwner.trans hjOwner.symm
            · exact ⟨i, hiOwner, hi, hxi⟩
          rcases hcandidate with ⟨candidate, hne, hcandActive, hxcandidate⟩
          cases candidate with
          | inl candidate =>
              have hxcandidate' : x ∈ edgeIncidentVertices (leftTree.edgeRegion candidate) := by
                simpa [edgeRegion] using hxcandidate
              exact Finset.mem_union_left _
                (cross_terminal_incident_inter_subset_separator hsubset hsymmetric hincident
                  hpartition leftTree rightTree candidate owner
                  (Finset.mem_inter.mpr ⟨hxcandidate', hxOwner⟩))
          | inr candidate =>
              have hcandidateActive : candidate ∈ rightTree.edgeActive := by
                have hnonempty := (@Finset.mem_filter _ _
                  (fun _ => Finset.decidableNonempty) _ _).mp hcandActive
                apply Finset.mem_filter.mpr
                exact ⟨Finset.mem_univ _, hnonempty.2⟩
              have hxcandidate' : x ∈ edgeIncidentVertices (rightTree.edgeRegion candidate) := by
                simpa [edgeRegion] using hxcandidate
              have hxChildShared : x ∈ edgeDivisionSharedBoundary
                  rightTree.edgeRegion rightTree.edgeActive := by
                apply (mem_edgeDivisionSharedBoundary_iff _ _ x).2
                refine ⟨owner, hownerActive, candidate, hcandidateActive, ?_, hxOwner,
                  hxcandidate'⟩
                intro heq
                exact hne (congrArg Sum.inr heq.symm)
              exact Finset.mem_union_right _
                (ihRight owner (Finset.mem_inter.mpr ⟨hxOwner, hxChildShared⟩))
end EdgeRestrictedStoppedRecursion
end QEC.Locality
