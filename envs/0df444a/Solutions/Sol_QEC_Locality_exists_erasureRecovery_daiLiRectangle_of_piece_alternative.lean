-- Prove2me | solution 1 for QEC.Locality.exists_erasureRecovery_daiLiRectangle_of_piece_alternative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:22:50.361589+00:00
-- url     : https://prove2.me/submissions/b08c4dd6-1ccd-446b-86b9-4f4025111bbe

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiRectangle_of_low_counter_clipped_growth
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiRectangle_of_packing_lt_distance

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
    (threshold ell w : ℝ) (lower upper : ℝ × ℝ)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hThreshold : 1 ≤ threshold)
    (hBaseHorizontal : baseHorizontalRadius ≤ daiLiRectangleHorizontalRadius lower upper)
    (hBaseVertical : baseVerticalRadius ≤ daiLiRectangleVerticalRadius lower upper)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : daiLiRectangleHorizontalRadius lower upper ≤
      baseHorizontalRadius + steps * threshold)
    (hReachVertical : daiLiRectangleVerticalRadius lower upper ≤
      baseVerticalRadius + steps * threshold)
    (hBaseCard : (centeredRectangleQubits embedding
      (daiLiRectangleCenter lower upper) baseHorizontalRadius
      baseVerticalRadius).card < d)
    (hBoundaryBudget :
      48 * (daiLiRectangleHorizontalRadius lower upper +
        daiLiRectangleVerticalRadius lower upper + threshold) * threshold +
        (d : ℝ) / 10 < d)
    (hSpan : upper.1 - lower.1 = w) (hWidth : 1 ≤ w) (hEll : 1 ≤ ell)
    (hMinimumHeight : 5 * ell ≤ upper.2 - lower.2)
    (hShortPackingScale : 60 * w * ell < d)
    (hPiece : 10 * regionInteractionCounter P embedding threshold
        (embedding.qubitsInRectangle lower upper) ≤ d ∨
      upper.2 - lower.2 ≤ 10 * ell) :
    ∃ recovery : QuantumChannel
        (daiLiRectangleSubsystem embedding lower upper).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiRectangleSubsystem embedding lower upper).complementSystem
        P.semanticCode
        (daiLiRectangleSubsystem embedding lower upper).erasureChannelFromRegister recovery := by
  rcases hPiece with hLow | hShort
  · exact exists_erasureRecovery_daiLiRectangle_of_low_counter_clipped_growth
      P embedding d hDistance threshold lower upper baseHorizontalRadius
      baseVerticalRadius steps hThreshold hBaseHorizontal hBaseVertical
      hBaseHorizontalDiameter hBaseVerticalDiameter hReachHorizontal hReachVertical
      hBaseCard hLow hBoundaryBudget
  · apply exists_erasureRecovery_daiLiRectangle_of_packing_lt_distance
      P embedding d hDistance lower upper
    · linarith
    · nlinarith
    · have hArea : 6 * ((upper.1 - lower.1) * (upper.2 - lower.2)) ≤
          60 * w * ell := by
        have hHeightScaled : w * (upper.2 - lower.2) ≤ w * (10 * ell) :=
          mul_le_mul_of_nonneg_left hShort (by linarith)
        calc
          6 * ((upper.1 - lower.1) * (upper.2 - lower.2)) =
              6 * (w * (upper.2 - lower.2)) := by rw [hSpan]
          _ ≤ 6 * (w * (10 * ell)) :=
            mul_le_mul_of_nonneg_left hHeightScaled (by norm_num)
          _ = 60 * w * ell := by ring
      exact lt_of_le_of_lt hArea hShortPackingScale
end QEC.Locality
