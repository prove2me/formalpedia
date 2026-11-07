-- Prove2me | solution 1 for QEC.Locality.mem_daiLiKGeDInternalSide_strict_hostBounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:17:58.630204+00:00
-- url     : https://prove2.me/submissions/87acd62d-4434-4836-8b3f-af351e2ffd76

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_mem_daiLiBadGridCells_iff
import Theorems.Thm_QEC_Locality_daiLiBadGridRectangle_parentBounds
import Theorems.Thm_QEC_Locality_daiLiBadGridRectangle_get_verticalOrder
import Theorems.Thm_QEC_Locality_daiLiKGeDRegionRectangle_bad_eq_get
import Theorems.Thm_QEC_Locality_daiLiKGeDRegionRectangle_bad_mem
import Theorems.Thm_QEC_Locality_mem_daiLiKGeDInternalSideCandidates_iff
import Theorems.Thm_QEC_Locality_mem_daiLiKGeDInternalSideRawBounds
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
import Theorems.Thm_QEC_Locality_daiLiPhysicalGreedyRectangles_piece_properties
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
    (threshold w ell : ℝ) (t : GridTranslation w)
    (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hEll : 0 < ell) (cell : ℤ × ℤ) (slot : ℕ)
    (hCandidate : (cell, slot) ∈ daiLiKGeDInternalSideCandidates P embedding threshold d
      w (gridOrigin w t) rectangles) (p : ι)
    (hp : p ∈ daiLiRectangleSideStripQubits embedding ell
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (cell, slot)).1
      (daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles (cell, slot)).2 3) :
    (gridOrigin w t).1 + (cell.1 : ℝ) * w + 2 * ell ≤ (embedding.point p).1 ∧
      (embedding.point p).1 ≤ (gridOrigin w t).1 + ((cell.1 : ℝ) + 1) * w - 2 * ell ∧
      (gridOrigin w t).2 + (cell.2 : ℝ) * w + 4 * ell ≤ (embedding.point p).2 ∧
      (embedding.point p).2 ≤ (gridOrigin w t).2 + ((cell.2 : ℝ) + 1) * w - 4 * ell := by
  rcases (mem_daiLiKGeDInternalSideCandidates_iff P embedding threshold d w
    (gridOrigin w t) rectangles cell slot).1 hCandidate with ⟨hBad, hNext⟩
  have hSlot : slot < (rectangles cell).length :=
    Nat.lt_trans (Nat.lt_succ_self slot) hNext
  let rectangle := daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles
    (cell, slot)
  let nextRectangle := daiLiKGeDInternalSideRectangle embedding w (gridOrigin w t) rectangles
    (cell, slot + 1)
  have hRectangle : rectangle ∈ rectangles cell := by
    dsimp [rectangle, daiLiKGeDInternalSideRectangle]
    exact daiLiKGeDRegionRectangle_bad_mem embedding w (gridOrigin w t)
      rectangles cell slot hSlot
  have hNextRectangle : nextRectangle ∈ rectangles cell := by
    dsimp [nextRectangle, daiLiKGeDInternalSideRectangle]
    exact daiLiKGeDRegionRectangle_bad_mem embedding w (gridOrigin w t)
      rectangles cell (slot + 1) hNext
  have hPhysical := hRectangle
  have hNextPhysical := hNextRectangle
  rw [hRectangles cell hBad] at hPhysical hNextPhysical
  have hProperties := daiLiPhysicalGreedyRectangles_piece_properties
    P embedding threshold
      ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
      ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) ell hEll
      (hAtoms cell hBad) d rectangle hPhysical
  have hNextProperties := daiLiPhysicalGreedyRectangles_piece_properties
    P embedding threshold
      ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
      ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) ell hEll
      (hAtoms cell hBad) d nextRectangle hNextPhysical
  have hParent := daiLiBadGridRectangle_parentBounds P embedding threshold d w ell
    (gridOrigin w t) atoms rectangles hAtoms hRectangles hEll cell hBad rectangle hRectangle
  have hNextParent := daiLiBadGridRectangle_parentBounds P embedding threshold d w ell
    (gridOrigin w t) atoms rectangles hAtoms hRectangles hEll cell hBad nextRectangle
      hNextRectangle
  have hOrder := daiLiBadGridRectangle_get_verticalOrder P embedding threshold d w ell
    (gridOrigin w t) atoms rectangles hAtoms hRectangles hEll cell hBad slot (slot + 1)
    hSlot hNext (Nat.lt_succ_self slot)
  have hRectangleEq : rectangle = (rectangles cell).get ⟨slot, hSlot⟩ := by
    dsimp [rectangle, daiLiKGeDInternalSideRectangle]
    exact daiLiKGeDRegionRectangle_bad_eq_get embedding w (gridOrigin w t)
      rectangles cell slot hSlot
  have hNextRectangleEq : nextRectangle = (rectangles cell).get ⟨slot + 1, hNext⟩ := by
    dsimp [nextRectangle, daiLiKGeDInternalSideRectangle]
    exact daiLiKGeDRegionRectangle_bad_eq_get embedding w (gridOrigin w t)
      rectangles cell (slot + 1) hNext
  have hOrder' : rectangle.2.2 ≤ nextRectangle.1.2 := by
    rw [hRectangleEq, hNextRectangleEq]
    exact hOrder
  have hpBounds := mem_daiLiKGeDInternalSideRawBounds embedding w ell (gridOrigin w t)
    rectangles (cell, slot) p hp
  simp only [gridCellLower, gridCellUpper] at hParent hNextParent
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [hParent.1, hpBounds.1]
  · nlinarith [hParent.2.1, hpBounds.2.1]
  · nlinarith [hParent.2.2.1, hProperties.1, hpBounds.2.2.1]
  · nlinarith [hOrder', hNextProperties.1, hNextParent.2.2.2, hpBounds.2.2.2]
end QEC.Locality
