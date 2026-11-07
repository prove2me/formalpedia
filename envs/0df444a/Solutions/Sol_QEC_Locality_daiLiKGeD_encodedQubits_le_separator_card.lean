-- Prove2me | solution 1 for QEC.Locality.daiLiKGeD_encodedQubits_le_separator_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:37:02.515761+00:00
-- url     : https://prove2.me/submissions/70fc139b-78de-420c-af2b-2daa8fbc0d5b

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_daiLiKGeD_partition_pairwise
import Theorems.Thm_QEC_Locality_daiLiKGeD_partition_cover
import Theorems.Thm_QEC_Locality_card_daiLiKGeDResidual_le_separator
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiKGeDA
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiKGeDTrimmedB
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_two_correctable_regions_encodedQubits_le_separator_card


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
    (hThreshold : 1 ≤ threshold) (hWidthNat : 1 ≤ w) (hEllNat : 1 ≤ ell)
    (hWidth : 0 < w) (hEll : 0 < ell) (hThresholdEll : threshold ≤ ell)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hBaseHorizontal : baseHorizontalRadius ≤ w / 2)
    (hBaseVerticalGood : baseVerticalRadius ≤ w / 2)
    (hBaseVerticalBad : baseVerticalRadius ≤ 5 * ell / 2)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : w / 2 ≤ baseHorizontalRadius + steps * threshold)
    (hReachVerticalGood : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hReachVerticalBad : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hGoodBaseCard : ∀ cell,
      Sum.inl cell ∈ daiLiKGeDRegionCandidates P embedding threshold d
        w (gridOrigin w t) rectangles →
      (centeredRectangleQubits embedding (daiLiGridCellCenter w (gridOrigin w t) cell)
        baseHorizontalRadius baseVerticalRadius).card < d)
    (hBadBaseCard : ∀ cell slot,
      Sum.inr (cell, slot) ∈ daiLiKGeDRegionCandidates P embedding threshold d
        w (gridOrigin w t) rectangles →
      (centeredRectangleQubits embedding
        (daiLiRectangleCenter
          (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
            (Sum.inr (cell, slot))).1
          (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
            (Sum.inr (cell, slot))).2)
        baseHorizontalRadius baseVerticalRadius).card < d)
    (hBoundaryBudget :
      48 * (w / 2 + w / 2 + threshold) * threshold + (d : ℝ) / 10 < d)
    (hShortPackingScale : 60 * w * ell < d)
    (hCellWidth : 5 * ell ≤ w) (hInternalSideScale : 12 * ell * w < d)
    (hGridWidth : 4 * ell ≤ w) (hEdge : 1 ≤ 2 * ell)
    (hGridLong : 1 ≤ w - 4 * ell) (hGridSideSmall : 12 * ell * (w - 4 * ell) < d) :
    P.encodedQubits ≤
      (daiLiKGeDSeparator P embedding threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).card := by
  obtain ⟨recoveryA, hRecoveryA⟩ := exists_erasureRecovery_daiLiKGeDA P embedding d hDistance
    threshold w ell t atoms rectangles hAtoms hRectangles hThreshold hWidthNat hEllNat hEll hWidth
    hThresholdEll baseHorizontalRadius baseVerticalRadius steps hBaseHorizontal hBaseVerticalGood
    hBaseVerticalBad hBaseHorizontalDiameter hBaseVerticalDiameter hReachHorizontal
    hReachVerticalGood hReachVerticalBad hGoodBaseCard hBadBaseCard hBoundaryBudget
    hShortPackingScale
  obtain ⟨recoveryB, hRecoveryB⟩ := exists_erasureRecovery_daiLiKGeDTrimmedB P embedding d
    hDistance threshold w ell t atoms rectangles hAtoms hRectangles hEllNat hCellWidth
    hInternalSideScale hEll hGridWidth hThresholdEll hEdge hGridLong hGridSideSmall
  have hPairwise := daiLiKGeD_partition_pairwise P embedding d threshold w ell t
    (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
  have hDimension : P.encodedQubits ≤
      (daiLiKGeDResidualSubsystem P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).selected.card :=
    two_correctable_regions_encodedQubits_le_separator_card P
      (daiLiKGeDASubsystem P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
      (daiLiKGeDTrimmedBSubsystem P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
      (daiLiKGeDResidualSubsystem P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
      hPairwise.1 hPairwise.2.1 hPairwise.2.2
      (daiLiKGeD_partition_cover P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
      recoveryA hRecoveryA recoveryB hRecoveryB
  exact hDimension.trans
    (card_daiLiKGeDResidual_le_separator P embedding d threshold w ell t atoms rectangles
      hAtoms hRectangles hWidth hEll)
end QEC.Locality
