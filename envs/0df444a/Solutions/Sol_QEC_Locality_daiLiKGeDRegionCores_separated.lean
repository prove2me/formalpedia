-- Prove2me | solution 1 for QEC.Locality.daiLiKGeDRegionCores_separated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:23:28.885117+00:00
-- url     : https://prove2.me/submissions/da828c46-c294-49de-bbca-847d8788b253

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_mem_daiLiBadGridCells_iff
import Theorems.Thm_QEC_Locality_daiLiBadGridRectangle_get_verticalOrder
import Theorems.Thm_QEC_Locality_le_distance_of_le_abs_coordinate_y
import Theorems.Thm_QEC_Locality_daiLiStrictGridCellInteriors_separated
import Theorems.Thm_QEC_Locality_mem_daiLiKGeDRegionCandidates_good_iff
import Theorems.Thm_QEC_Locality_mem_daiLiKGeDRegionCandidates_bad_iff
import Theorems.Thm_QEC_Locality_daiLiKGeDRegionRectangle_bad_eq_get
import Theorems.Thm_QEC_Locality_mem_daiLiKGeDRegionCore_strict_rectangleBounds
import Theorems.Thm_QEC_Locality_mem_daiLiKGeDRegionCore_strict_hostBounds
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
    (hEll : 0 < ell) (hWidth : 0 < w)
    (region other : DaiLiKGeDRegionIndex)
    (hRegion : region ∈ daiLiKGeDRegionCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (hOther : other ∈ daiLiKGeDRegionCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (hne : region ≠ other) {p q : ι}
    (hp : p ∈ daiLiKGeDRegionCoreQubits P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles region)
    (hq : q ∈ daiLiKGeDRegionCoreQubits P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles other) :
    ell ≤ embedding.distance p q := by
  have hpHost := mem_daiLiKGeDRegionCore_strict_hostBounds P embedding d threshold w ell t
    atoms rectangles hAtoms hRectangles hEll region hRegion p hp
  have hqHost := mem_daiLiKGeDRegionCore_strict_hostBounds P embedding d threshold w ell t
    atoms rectangles hAtoms hRectangles hEll other hOther q hq
  by_cases hHost : daiLiKGeDRegionHostCell region = daiLiKGeDRegionHostCell other
  · cases region with
    | inl cell =>
        cases other with
        | inl other =>
            simp only [daiLiKGeDRegionHostCell] at hHost
            subst other
            exact (hne rfl).elim
        | inr pair =>
            rcases pair with ⟨other, slot⟩
            simp only [daiLiKGeDRegionHostCell] at hHost
            subst other
            have hNotBad := (mem_daiLiKGeDRegionCandidates_good_iff P embedding threshold d w
              (gridOrigin w t) rectangles cell).1 hRegion |>.2
            have hBad := (mem_daiLiKGeDRegionCandidates_bad_iff P embedding threshold d w
              (gridOrigin w t) rectangles cell slot).1 hOther |>.1
            exact (hNotBad hBad).elim
    | inr pair =>
        rcases pair with ⟨cell, slot⟩
        cases other with
        | inl other =>
            simp only [daiLiKGeDRegionHostCell] at hHost
            subst other
            have hBad := (mem_daiLiKGeDRegionCandidates_bad_iff P embedding threshold d w
              (gridOrigin w t) rectangles cell slot).1 hRegion |>.1
            have hNotBad := (mem_daiLiKGeDRegionCandidates_good_iff P embedding threshold d w
              (gridOrigin w t) rectangles cell).1 hOther |>.2
            exact (hNotBad hBad).elim
        | inr otherPair =>
            rcases otherPair with ⟨other, otherSlot⟩
            simp only [daiLiKGeDRegionHostCell] at hHost
            subst other
            rcases (mem_daiLiKGeDRegionCandidates_bad_iff P embedding threshold d w
              (gridOrigin w t) rectangles cell slot).1 hRegion with ⟨hBad, hSlot⟩
            rcases (mem_daiLiKGeDRegionCandidates_bad_iff P embedding threshold d w
              (gridOrigin w t) rectangles cell otherSlot).1 hOther with ⟨_, hOtherSlot⟩
            have hSlotNe : slot ≠ otherSlot := by
              intro hEqual
              apply hne
              simp [hEqual]
            have hpRectangle := mem_daiLiKGeDRegionCore_strict_rectangleBounds
              P embedding threshold w ell t
              (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
              (Sum.inr (cell, slot)) p hp
            have hqRectangle := mem_daiLiKGeDRegionCore_strict_rectangleBounds
              P embedding threshold w ell t
              (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
              (Sum.inr (cell, otherSlot)) q hq
            rcases lt_or_gt_of_ne hSlotNe with hForward | hBackward
            · have hOrder := daiLiBadGridRectangle_get_verticalOrder P embedding threshold d w ell
                (gridOrigin w t) atoms rectangles hAtoms hRectangles hEll cell hBad
                slot otherSlot hSlot hOtherSlot hForward
              have hFirstEq := daiLiKGeDRegionRectangle_bad_eq_get embedding w (gridOrigin w t)
                rectangles cell slot hSlot
              have hSecondEq := daiLiKGeDRegionRectangle_bad_eq_get embedding w (gridOrigin w t)
                rectangles cell otherSlot hOtherSlot
              have hOrder' :
                  (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
                    (Sum.inr (cell, slot))).2.2 ≤
                    (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
                      (Sum.inr (cell, otherSlot))).1.2 := by
                rw [hFirstEq, hSecondEq]
                exact hOrder
              apply le_distance_of_le_abs_coordinate_y embedding
              rw [le_abs]
              right
              nlinarith [hpRectangle.2.2.2, hqRectangle.2.2.1, hOrder']
            · have hOrder := daiLiBadGridRectangle_get_verticalOrder P embedding threshold d w ell
                (gridOrigin w t) atoms rectangles hAtoms hRectangles hEll cell hBad
                otherSlot slot hOtherSlot hSlot hBackward
              have hFirstEq := daiLiKGeDRegionRectangle_bad_eq_get embedding w (gridOrigin w t)
                rectangles cell otherSlot hOtherSlot
              have hSecondEq := daiLiKGeDRegionRectangle_bad_eq_get embedding w (gridOrigin w t)
                rectangles cell slot hSlot
              have hOrder' :
                  (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
                    (Sum.inr (cell, otherSlot))).2.2 ≤
                    (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
                      (Sum.inr (cell, slot))).1.2 := by
                rw [hFirstEq, hSecondEq]
                exact hOrder
              apply le_distance_of_le_abs_coordinate_y embedding
              rw [le_abs]
              left
              nlinarith [hpRectangle.2.2.1, hqRectangle.2.2.2, hOrder']
  · exact daiLiStrictGridCellInteriors_separated embedding hEll.le hWidth.le (gridOrigin w t)
      (daiLiKGeDRegionHostCell region) (daiLiKGeDRegionHostCell other) hHost hpHost hqHost
end QEC.Locality
