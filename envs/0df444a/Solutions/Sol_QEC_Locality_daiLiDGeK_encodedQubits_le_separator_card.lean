-- Prove2me | solution 1 for QEC.Locality.daiLiDGeK_encodedQubits_le_separator_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:25:34.225209+00:00
-- url     : https://prove2.me/submissions/dba50d5b-5ef6-48d7-9658-f2176a28e8be

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
import Theorems.Thm_QEC_Locality_daiLiDGeK_partition_pairwise
import Theorems.Thm_QEC_Locality_daiLiDGeK_partition_cover
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiDGeKTrimmedB
import Theorems.Thm_QEC_Locality_card_daiLiDGeKResidual_le_separator
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiDGeKA
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sum_daiLiInteractionCounter_eq_two_mul_longInteractionCount
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
attribute [local instance] QEC.Locality.instClassicalDecidableDGeK
namespace QEC.Locality
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (hGlobal : 10 * (∑ q : ι, P.daiLiInteractionCounter embedding threshold q) < d)
    (hThreshold : 1 ≤ threshold) (hWidthNat : 1 ≤ w) (hEllNat : 1 ≤ ell)
    (hEll : 0 < ell) (hWidth : 0 < w) (hScale : 4 * ell ≤ w)
    (hThresholdEll : threshold ≤ ell)
    (hEdge : 1 ≤ 2 * ell) (hLongStrip : 1 ≤ w - 4 * ell)
    (hSmallStrip : 12 * ell * (w - 4 * ell) < d)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hBaseHorizontal : baseHorizontalRadius ≤ w / 2)
    (hBaseVerticalGood : baseVerticalRadius ≤ w / 2)
    (hBaseVerticalBad : baseVerticalRadius ≤ 5 * ell / 2)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : w / 2 ≤ baseHorizontalRadius + steps * threshold)
    (hReachVerticalGood : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hReachVerticalBad : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hGoodBaseCard : ∀ cell, cell ∈ embedding.gridOccupiedCells w (gridOrigin w t) →
      (centeredRectangleQubits embedding (daiLiGridCellCenter w (gridOrigin w t) cell)
        baseHorizontalRadius baseVerticalRadius).card < d)
    (hBoundaryBudget :
      48 * (w / 2 + w / 2 + threshold) * threshold + (d : ℝ) / 10 < d)
    (hShortPackingScale : 60 * w * ell < d) :
    P.encodedQubits ≤ (daiLiDGeKSeparator P embedding threshold w ell t).card := by
  have hLongCount : 2 * P.longInteractionCount embedding threshold < d := by
    rw [← P.sum_daiLiInteractionCounter_eq_two_mul_longInteractionCount embedding threshold]
    omega
  obtain ⟨recoveryA, hRecoveryA⟩ := exists_erasureRecovery_daiLiDGeKA P embedding d
    hDistance threshold w ell t hGlobal hThreshold hWidthNat hEllNat hEll hWidth
    hThresholdEll baseHorizontalRadius baseVerticalRadius steps hBaseHorizontal
    hBaseVerticalGood hBaseVerticalBad hBaseHorizontalDiameter hBaseVerticalDiameter
    hReachHorizontal hReachVerticalGood hReachVerticalBad hGoodBaseCard hBoundaryBudget
    hShortPackingScale
  obtain ⟨recoveryB, hRecoveryB⟩ := exists_erasureRecovery_daiLiDGeKTrimmedB P embedding d
    hDistance threshold w ell t hEll hScale hThresholdEll hEdge hLongStrip hSmallStrip
    hLongCount
  have hPairwise := daiLiDGeK_partition_pairwise P embedding d threshold w ell t
  have hDimension : P.encodedQubits ≤
      (daiLiDGeKResidualSubsystem P embedding d threshold w ell t).selected.card :=
    two_correctable_regions_encodedQubits_le_separator_card P
      (daiLiDGeKASubsystem P embedding d threshold w ell t)
      (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t)
      (daiLiDGeKResidualSubsystem P embedding d threshold w ell t)
      hPairwise.1 hPairwise.2.1 hPairwise.2.2
      (daiLiDGeK_partition_cover P embedding d threshold w ell t)
      recoveryA hRecoveryA recoveryB hRecoveryB
  exact hDimension.trans
    (card_daiLiDGeKResidual_le_separator P embedding d threshold w ell t hGlobal hWidth hEll)
end QEC.Locality
