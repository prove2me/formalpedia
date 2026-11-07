-- Prove2me | solution 1 for QEC.Locality.exists_erasureRecovery_daiLiKGeDGoodRegionCore
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:20:13.062137+00:00
-- url     : https://prove2.me/submissions/b5005cd2-839b-4825-a6e1-541b6212dc24

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_daiLiGridCellClosedQubits_eq_rectangle
import Theorems.Thm_QEC_Locality_mem_daiLiBadGridCells_iff
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiGridCell_of_good_clipped_growth
import Theorems.Thm_QEC_Locality_mem_daiLiKGeDRegionCandidates_good_iff
import Theorems.Thm_QEC_Locality_daiLiKGeDRegionCore_subset_rectangle
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
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_finiteSubsystem_subset
import Theorems.Thm_QEC_Locality_isBadInteractionRegion_iff_not_isGoodInteractionRegion
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
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ)
    (hCandidate : Sum.inl cell ∈ daiLiKGeDRegionCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hThreshold : 1 ≤ threshold)
    (hBaseHorizontal : baseHorizontalRadius ≤ w / 2)
    (hBaseVertical : baseVerticalRadius ≤ w / 2)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : w / 2 ≤ baseHorizontalRadius + steps * threshold)
    (hReachVertical : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hBaseCard : (centeredRectangleQubits embedding
      (daiLiGridCellCenter w (gridOrigin w t) cell)
      baseHorizontalRadius baseVerticalRadius).card < d)
    (hBoundaryBudget :
      48 * (w / 2 + w / 2 + threshold) * threshold + (d : ℝ) / 10 < d) :
    ∃ recovery : QuantumChannel
        (daiLiKGeDRegionCoreSubsystem P embedding threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
          (Sum.inl cell)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiKGeDRegionCoreSubsystem P embedding threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
          (Sum.inl cell)).complementSystem
        P.semanticCode
        (daiLiKGeDRegionCoreSubsystem P embedding threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
          (Sum.inl cell)).erasureChannelFromRegister recovery := by
  rcases (mem_daiLiKGeDRegionCandidates_good_iff P embedding threshold d w
    (gridOrigin w t) rectangles cell).1 hCandidate with ⟨hOccupied, hNotBad⟩
  have hNotBadSquare : ¬ IsBadInteractionSquare P embedding threshold d
      (daiLiGridCellCenter w (gridOrigin w t) cell) (w / 2) := by
    intro hBad
    apply hNotBad
    exact (mem_daiLiBadGridCells_iff P embedding threshold d w (gridOrigin w t) cell).2
      ⟨hOccupied, hBad⟩
  have hGood : IsGoodInteractionSquare P embedding threshold d
      (daiLiGridCellCenter w (gridOrigin w t) cell) (w / 2) := by
    by_contra hNotGood
    apply hNotBadSquare
    change IsBadInteractionRegion P embedding threshold d
      (squareQubits embedding (daiLiGridCellCenter w (gridOrigin w t) cell) (w / 2))
    apply (isBadInteractionRegion_iff_not_isGoodInteractionRegion P embedding threshold d
      (squareQubits embedding (daiLiGridCellCenter w (gridOrigin w t) cell) (w / 2))).2
    simpa [IsGoodInteractionSquare] using hNotGood
  apply exists_erasureRecovery_of_finiteSubsystem_subset
    (daiLiKGeDRegionCoreSubsystem P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
      (Sum.inl cell))
    (daiLiGridCellClosedSubsystem embedding w (gridOrigin w t) cell)
  · change daiLiKGeDRegionCoreQubits P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
      (Sum.inl cell) ⊆ daiLiGridCellClosedQubits embedding w (gridOrigin w t) cell
    rw [daiLiGridCellClosedQubits_eq_rectangle]
    simpa [daiLiKGeDRegionRectangle] using
      (daiLiKGeDRegionCore_subset_rectangle P embedding threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
        (Sum.inl cell))
  · exact exists_erasureRecovery_daiLiGridCell_of_good_clipped_growth
      P embedding d hDistance threshold w (gridOrigin w t) cell
      baseHorizontalRadius baseVerticalRadius steps hThreshold hBaseHorizontal hBaseVertical
      hBaseHorizontalDiameter hBaseVerticalDiameter hReachHorizontal hReachVertical
      hBaseCard hGood hBoundaryBudget
end QEC.Locality
