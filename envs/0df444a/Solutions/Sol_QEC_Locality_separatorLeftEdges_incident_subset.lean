-- Prove2me | solution 1 for QEC.Locality.separatorLeftEdges_incident_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:15:22.901276+00:00
-- url     : https://prove2.me/submissions/d7c5791b-e73e-4718-9600-71456a422a4a

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_mem_directedEdgeFinset_iff
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



set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (G : ConnectivityGraph ι) (edges : Finset (ι × ι))
    (vertices left separator right : Finset ι)
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hsymmetric : ReverseSymmetricEdgeSet edges)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (hpartition :
      TwoThirdsBalancedPartitionAfterDeleting (edgeRestrictedGraph G edges)
        vertices left separator right) :
    edgeIncidentVertices (separatorLeftEdges edges left) ⊆ left ∪ separator := by
  classical
  intro z hz
  rcases (mem_edgeIncidentVertices_iff _ z).1 hz with
    ⟨⟨x, y⟩, hedge, hzEndpoint⟩
  have hedgeParent : (x, y) ∈ edges := (Finset.mem_filter.mp hedge).1
  have hxy : (edgeRestrictedGraph G edges).adjacent x y := by
    refine ⟨(mem_directedEdgeFinset_iff G x y).1 (hsubset hedgeParent), Or.inl hedgeParent⟩
  have hleft : x ∈ left ∨ y ∈ left := (Finset.mem_filter.mp hedge).2
  have hxvertices : x ∈ vertices := by
    apply hincident
    exact (mem_edgeIncidentVertices_iff edges x).2
      ⟨(x, y), hedgeParent, Or.inl rfl⟩
  have hyvertices : y ∈ vertices := by
    apply hincident
    exact (mem_edgeIncidentVertices_iff edges y).2
      ⟨(x, y), hedgeParent, Or.inr rfl⟩
  have hcover : separator ∪ (left ∪ right) = vertices := by
    rw [hpartition.2.1]
    exact Finset.union_sdiff_of_subset hpartition.1
  have hxparts : x ∈ left ∪ separator ∪ right := by
    rw [← hcover] at hxvertices
    simpa [Finset.union_assoc, Finset.union_comm, Finset.union_left_comm] using hxvertices
  have hyparts : y ∈ left ∪ separator ∪ right := by
    rw [← hcover] at hyvertices
    simpa [Finset.union_assoc, Finset.union_comm, Finset.union_left_comm] using hyvertices
  rcases hzEndpoint with rfl | rfl
  · rcases hleft with hxleft | hyleft
    · exact Finset.mem_union_left _ hxleft
    · rcases Finset.mem_union.mp hxparts with hxparts | hxright
      · rcases Finset.mem_union.mp hxparts with hxleft | hxseparator
        · exact Finset.mem_union_left _ hxleft
        · exact Finset.mem_union_right _ hxseparator
      · exact False.elim (hpartition.2.2.2.2.2 hyleft hxright
          ((edgeRestrictedGraph G edges).symmetric hxy))
  · rcases hleft with hxleft | hyleft
    · rcases Finset.mem_union.mp hyparts with hyparts | hyright
      · rcases Finset.mem_union.mp hyparts with hyleft | hyseparator
        · exact Finset.mem_union_left _ hyleft
        · exact Finset.mem_union_right _ hyseparator
      · exact False.elim (hpartition.2.2.2.2.2 hxleft hyright hxy)
    · exact Finset.mem_union_left _ hyleft
end QEC.Locality
