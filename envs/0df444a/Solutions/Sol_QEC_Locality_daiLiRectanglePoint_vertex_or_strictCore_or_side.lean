-- Prove2me | solution 1 for QEC.Locality.daiLiRectanglePoint_vertex_or_strictCore_or_side
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:14:54.742203+00:00
-- url     : https://prove2.me/submissions/aab9f46f-e3d7-4200-9e8f-05c9dc09faad

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_mem_daiLiBadGridCells_iff
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_qubitsInRectangle_iff
import Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_zero
import Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
import Theorems.Thm_QEC_Locality_mem_longInteractionEndpointQubits_iff
import Theorems.Thm_QEC_Locality_mem_longNeighborsOf_iff
import Theorems.Thm_QEC_Locality_mem_squareQubits_iff
import Theorems.Thm_QEC_Locality_squareGrowthRadius_succ_sub
import Theorems.Thm_QEC_Locality_squareGrowthRadius_zero
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
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionLength_sym2_mk
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_diag_not_mem_fixedGeneratorInteractions
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_gridCellQubits_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_gridOccupiedCells_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff
attribute [local simp] QEC.Locality.centeredRectangleClippedGrowthRadius_zero
attribute [local simp] QEC.Locality.mem_centeredRectangleQubits_iff
attribute [local simp] QEC.Locality.mem_longInteractionEndpointQubits_iff
attribute [local simp] QEC.Locality.mem_longNeighborsOf_iff
attribute [local simp] QEC.Locality.mem_squareQubits_iff
attribute [local simp] QEC.Locality.squareGrowthRadius_succ_sub
attribute [local simp] QEC.Locality.squareGrowthRadius_zero
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


attribute [local simp] QEC.Locality.mem_daiLiBadGridCells_iff

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableCorrectable
namespace QEC.Locality
theorem _root_.solution
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (hEll : 0 < ell)
    (lower upper : ℝ × ℝ) (q : ι)
    (hq : q ∈ embedding.qubitsInRectangle lower upper) :
    (∃ vertex : Fin 4,
      q ∈ daiLiVertexNeighborhoodQubits embedding ell
        (daiLiRectangleVertex (lower, upper) vertex)) ∨
      (lower.1 + ell < (embedding.point q).1 ∧
        (embedding.point q).1 < upper.1 - ell ∧
          lower.2 + ell < (embedding.point q).2 ∧
            (embedding.point q).2 < upper.2 - ell) ∨
      ∃ side : Fin 4,
        q ∈ daiLiRectangleSideStripQubits embedding ell lower upper side := by
  by_cases hVertex : ∃ vertex : Fin 4,
      q ∈ daiLiVertexNeighborhoodQubits embedding ell
        (daiLiRectangleVertex (lower, upper) vertex)
  · exact Or.inl hVertex
  apply Or.inr
  have hNoVertex : ∀ vertex : Fin 4,
      q ∉ daiLiVertexNeighborhoodQubits embedding ell
        (daiLiRectangleVertex (lower, upper) vertex) := by
    intro vertex hqVertex
    exact hVertex ⟨vertex, hqVertex⟩
  rw [UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff] at hq
  by_cases hxLower : (embedding.point q).1 ≤ lower.1 + ell
  · apply Or.inr
    refine ⟨0, ?_⟩
    have hyLower : lower.2 + 2 * ell ≤ (embedding.point q).2 := by
      by_contra hnot
      have hy : (embedding.point q).2 < lower.2 + 2 * ell := lt_of_not_ge hnot
      apply hNoVertex 0
      simp [daiLiVertexNeighborhoodQubits, daiLiRectangleVertex,
        UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
      exact ⟨⟨by nlinarith [hq.1.1], by nlinarith [hxLower]⟩,
        ⟨by nlinarith [hq.2.1], by nlinarith⟩⟩
    have hyUpper : (embedding.point q).2 ≤ upper.2 - 2 * ell := by
      by_contra hnot
      have hy : upper.2 - 2 * ell < (embedding.point q).2 := lt_of_not_ge hnot
      apply hNoVertex 1
      simp [daiLiVertexNeighborhoodQubits, daiLiRectangleVertex,
        UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
      exact ⟨⟨by nlinarith [hq.1.1], by nlinarith [hxLower]⟩,
        ⟨by nlinarith, by nlinarith [hq.2.2]⟩⟩
    simp [daiLiRectangleSideStripQubits,
      UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
    exact ⟨⟨by nlinarith [hq.1.1], hxLower⟩, ⟨hyLower, hyUpper⟩⟩
  have hxLower' : lower.1 + ell < (embedding.point q).1 := lt_of_not_ge hxLower
  by_cases hxUpper : upper.1 - ell ≤ (embedding.point q).1
  · apply Or.inr
    refine ⟨1, ?_⟩
    have hyLower : lower.2 + 2 * ell ≤ (embedding.point q).2 := by
      by_contra hnot
      have hy : (embedding.point q).2 < lower.2 + 2 * ell := lt_of_not_ge hnot
      apply hNoVertex 2
      simp [daiLiVertexNeighborhoodQubits, daiLiRectangleVertex,
        UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
      exact ⟨⟨by nlinarith [hxUpper], by nlinarith [hq.1.2]⟩,
        ⟨by nlinarith [hq.2.1], by nlinarith⟩⟩
    have hyUpper : (embedding.point q).2 ≤ upper.2 - 2 * ell := by
      by_contra hnot
      have hy : upper.2 - 2 * ell < (embedding.point q).2 := lt_of_not_ge hnot
      apply hNoVertex 3
      simp [daiLiVertexNeighborhoodQubits, daiLiRectangleVertex,
        UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
      exact ⟨⟨by nlinarith [hxUpper], by nlinarith [hq.1.2]⟩,
        ⟨by nlinarith, by nlinarith [hq.2.2]⟩⟩
    simp [daiLiRectangleSideStripQubits,
      UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
    exact ⟨⟨hxUpper, by nlinarith [hq.1.2]⟩, ⟨hyLower, hyUpper⟩⟩
  have hxUpper' : (embedding.point q).1 < upper.1 - ell := lt_of_not_ge hxUpper
  by_cases hyLower : (embedding.point q).2 ≤ lower.2 + ell
  · apply Or.inr
    refine ⟨2, ?_⟩
    have hxLeft : lower.1 + 2 * ell ≤ (embedding.point q).1 := by
      by_contra hnot
      have hx : (embedding.point q).1 < lower.1 + 2 * ell := lt_of_not_ge hnot
      apply hNoVertex 0
      simp [daiLiVertexNeighborhoodQubits, daiLiRectangleVertex,
        UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
      exact ⟨⟨by nlinarith [hq.1.1], by nlinarith⟩,
        ⟨by nlinarith [hq.2.1], by nlinarith [hyLower]⟩⟩
    have hxRight : (embedding.point q).1 ≤ upper.1 - 2 * ell := by
      by_contra hnot
      have hx : upper.1 - 2 * ell < (embedding.point q).1 := lt_of_not_ge hnot
      apply hNoVertex 2
      simp [daiLiVertexNeighborhoodQubits, daiLiRectangleVertex,
        UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
      exact ⟨⟨by nlinarith, by nlinarith [hq.1.2]⟩,
        ⟨by nlinarith [hq.2.1], by nlinarith [hyLower]⟩⟩
    simp [daiLiRectangleSideStripQubits,
      UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
    exact ⟨⟨hxLeft, hxRight⟩, ⟨by nlinarith [hq.2.1], hyLower⟩⟩
  have hyLower' : lower.2 + ell < (embedding.point q).2 := lt_of_not_ge hyLower
  by_cases hyUpper : upper.2 - ell ≤ (embedding.point q).2
  · apply Or.inr
    refine ⟨3, ?_⟩
    have hxLeft : lower.1 + 2 * ell ≤ (embedding.point q).1 := by
      by_contra hnot
      have hx : (embedding.point q).1 < lower.1 + 2 * ell := lt_of_not_ge hnot
      apply hNoVertex 1
      simp [daiLiVertexNeighborhoodQubits, daiLiRectangleVertex,
        UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
      exact ⟨⟨by nlinarith [hq.1.1], by nlinarith⟩,
        ⟨by nlinarith [hyUpper], by nlinarith [hq.2.2]⟩⟩
    have hxRight : (embedding.point q).1 ≤ upper.1 - 2 * ell := by
      by_contra hnot
      have hx : upper.1 - 2 * ell < (embedding.point q).1 := lt_of_not_ge hnot
      apply hNoVertex 3
      simp [daiLiVertexNeighborhoodQubits, daiLiRectangleVertex,
        UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
      exact ⟨⟨by nlinarith, by nlinarith [hq.1.2]⟩,
        ⟨by nlinarith [hyUpper], by nlinarith [hq.2.2]⟩⟩
    simp [daiLiRectangleSideStripQubits,
      UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff]
    exact ⟨⟨hxLeft, hxRight⟩, ⟨hyUpper, by nlinarith [hq.2.2]⟩⟩
  exact Or.inl ⟨hxLower', hxUpper', hyLower', lt_of_not_ge hyUpper⟩
end QEC.Locality
