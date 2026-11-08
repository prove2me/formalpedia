-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.verticalFaceGraph_external_degree_le_endpoint_adjacency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:12:41.105315+00:00
-- url     : https://prove2.me/submissions/67215304-b56f-427c-96f7-1ebcc7baaae4

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sum_verticalFaceGraph_eq_card_filter
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sum_adjacencyGraph_eq_card_directionsInto
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_incidence_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_mem_variableSupport_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheck_globalOperator_eq_extendLocalToRegister
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.ProductExpansion.HammingWeight_neg
attribute [local simp] QEC.Coding.ProductExpansion.column_transpose
attribute [local simp] QEC.Coding.ProductExpansion.row_transpose
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.mem_variableSupport_iff_mem_region
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
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype F] [DecidableEq R] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (L : Finset (VertexIndex G)) (e : VerticalEdgeIndex W G) :
    (∑ e' ∈ activeVerticalEdges label c \
        unlabelledActiveVerticalEdges label c L,
        verticalFaceGraph label e e') ≤
      (∑ u ∈ L,
        adjacencyGraph label (verticalEdgeEndpoint label e 0) u) +
      ∑ u ∈ L, adjacencyGraph label
        (verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1) u := by
  classical
  rw [sum_verticalFaceGraph_eq_card_filter]
  let D := Finset.univ.filter fun a : W =>
    verticalFaceNeighbor label e a ∈
      activeVerticalEdges label c \
        unlabelledActiveVerticalEdges label c L
  let H₀ := horizontalDirectionsInto label L (verticalEdgeEndpoint label e 0)
  let H₁ := horizontalDirectionsInto label L
    (verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1)
  have hSubset : D ⊆ H₀ ∪ H₁ := by
    intro a ha
    have haDiff : verticalFaceNeighbor label e a ∈
        activeVerticalEdges label c \
          unlabelledActiveVerticalEdges label c L := by
      simpa [D] using ha
    have haActive := (Finset.mem_sdiff.mp haDiff).1
    have haNotBad := (Finset.mem_sdiff.mp haDiff).2
    have hEndpoint :
        verticalEdgeEndpoint label (verticalFaceNeighbor label e a) 0 ∈ L ∨
        verticalNeighbor label
          (verticalEdgeEndpoint label (verticalFaceNeighbor label e a) 0)
          (verticalFaceNeighbor label e a).2.1 ∈ L := by
      by_cases h₀ :
          verticalEdgeEndpoint label (verticalFaceNeighbor label e a) 0 ∈ L
      · exact Or.inl h₀
      by_cases h₁ :
          verticalNeighbor label
            (verticalEdgeEndpoint label (verticalFaceNeighbor label e a) 0)
            (verticalFaceNeighbor label e a).2.1 ∈ L
      · exact Or.inr h₁
      · exfalso
        apply haNotBad
        exact Finset.mem_filter.mpr ⟨haActive, h₀, h₁⟩
    apply Finset.mem_union.mpr
    rcases hEndpoint with h₀ | h₁
    · left
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ a, by simpa [H₀] using h₀⟩
    · right
      have h₁' : horizontalNeighbor label
          (verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1) a ∈
          L := by
        rw [← verticalNeighbor_horizontalNeighbor_commute]
        simpa using h₁
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ a, by simpa [H₁] using h₁'⟩
  have hAdj₀ := sum_adjacencyGraph_eq_card_directionsInto
    label L (verticalEdgeEndpoint label e 0)
  have hAdj₁ := sum_adjacencyGraph_eq_card_directionsInto label L
    (verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1)
  calc
    D.card ≤ (H₀ ∪ H₁).card := Finset.card_le_card hSubset
    _ ≤ H₀.card + H₁.card := Finset.card_union_le H₀ H₁
    _ ≤ (∑ u ∈ L,
          adjacencyGraph label (verticalEdgeEndpoint label e 0) u) +
        ∑ u ∈ L, adjacencyGraph label
          (verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1) u := by
      dsimp [H₀, H₁]
      omega
end QEC.Coding.TannerLiftedProduct
