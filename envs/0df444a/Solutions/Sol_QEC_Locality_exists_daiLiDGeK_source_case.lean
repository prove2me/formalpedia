-- Prove2me | solution 1 for QEC.Locality.exists_daiLiDGeK_source_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:35:28.782546+00:00
-- url     : https://prove2.me/submissions/2711813b-adb1-4b37-a79f-c6f79767d740

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiDGeKB
import Theorems.Thm_QEC_Locality_daiLiBadGridCells_eq_empty_of_small_longCount
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiDGeKA
import Theorems.Thm_QEC_Locality_exists_daiLiDGeKSeparator_card_lt_k_of_principal_scale
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sum_daiLiInteractionCounter_eq_two_mul_longInteractionCount


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
    (threshold w ell k : ℝ)
    (hk : 0 < k) (hd : 0 < (d : ℝ)) (_hDGeK : k ≤ d)
    (hn : 0 < (Fintype.card ι : ℝ))
    (hDistanceDomain : (d : ℝ) ≤ Real.sqrt (k * Fintype.card ι))
    (hScale : ell = daiLiPrincipalFourthRootScale k d (Fintype.card ι))
    (hWidth : w = daiLiDGeKGridWidth d ell)
    (hLongCount : (P.longInteractionCount embedding threshold : ℝ) ≤ (d : ℝ) / 100)
    (hGridScale : 4 * ell ≤ w)
    (hThreshold : 1 ≤ threshold) (hWidthNat : 1 ≤ w) (hEllNat : 1 ≤ ell)
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
    (hGoodBaseCard : ∀ (t : GridTranslation w) cell,
      cell ∈ embedding.gridOccupiedCells w (gridOrigin w t) →
        (centeredRectangleQubits embedding (daiLiGridCellCenter w (gridOrigin w t) cell)
          baseHorizontalRadius baseVerticalRadius).card < d)
    (hBoundaryBudget :
      48 * (w / 2 + w / 2 + threshold) * threshold + (d : ℝ) / 10 < d)
    (hShortPackingScale : 60 * w * ell < d) :
    ∃ t : GridTranslation w,
      ((daiLiDGeKSeparator P embedding threshold w ell t).card : ℝ) < k ∧
      daiLiBadGridCells P embedding threshold d w (gridOrigin w t) = ∅ ∧
      (∃ recovery : QuantumChannel
          (daiLiDGeKASubsystem P embedding d threshold w ell t).complementSystem
          (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι)
          (daiLiDGeKASubsystem P embedding d threshold w ell t).complementSystem
          P.semanticCode
          (daiLiDGeKASubsystem P embedding d threshold w ell t).erasureChannelFromRegister
          recovery) ∧
      ∃ recovery : QuantumChannel
          (daiLiDGeKBSubsystem P embedding threshold w ell t).complementSystem
          (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι)
          (daiLiDGeKBSubsystem P embedding threshold w ell t).complementSystem
          P.semanticCode
          (daiLiDGeKBSubsystem P embedding threshold w ell t).erasureChannelFromRegister
          recovery := by
  obtain ⟨t, hSeparator⟩ :=
    exists_daiLiDGeKSeparator_card_lt_k_of_principal_scale P embedding threshold w ell k d
      hk hd _hDGeK hn hDistanceDomain hScale hWidth hLongCount hGridScale
  have hTotal := P.sum_daiLiInteractionCounter_eq_two_mul_longInteractionCount
    embedding threshold
  have hTotalReal : ((∑ q : ι, P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) =
      2 * (P.longInteractionCount embedding threshold : ℝ) := by
    exact_mod_cast hTotal
  have hGlobalReal : 10 *
      ((∑ q : ι, P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) < d := by
    rw [hTotalReal]
    nlinarith
  have hGlobal : 10 * (∑ q : ι, P.daiLiInteractionCounter embedding threshold q) < d := by
    exact_mod_cast hGlobalReal
  have hLongCountNat : 2 * P.longInteractionCount embedding threshold < d := by
    have hLongCountReal : 2 * (P.longInteractionCount embedding threshold : ℝ) < d := by
      nlinarith
    exact_mod_cast hLongCountReal
  have hEll : 0 < ell := by
    rw [hScale, daiLiPrincipalFourthRootScale]
    apply mul_pos (by norm_num)
    apply Real.rpow_pos_of_pos
    positivity
  have hNoBad := daiLiBadGridCells_eq_empty_of_small_longCount P embedding threshold w d
    (gridOrigin w t) hGlobal
  refine ⟨t, hSeparator, hNoBad, ?_, ?_⟩
  · apply exists_erasureRecovery_daiLiDGeKA P embedding d hDistance threshold w ell t
      hGlobal hThreshold hWidthNat hEllNat hEll (by linarith) hThresholdEll
      baseHorizontalRadius baseVerticalRadius steps hBaseHorizontal hBaseVerticalGood
      hBaseVerticalBad hBaseHorizontalDiameter hBaseVerticalDiameter hReachHorizontal
      hReachVerticalGood hReachVerticalBad
    · intro cell hCell
      exact hGoodBaseCard t cell hCell
    · exact hBoundaryBudget
    · exact hShortPackingScale
  · exact exists_erasureRecovery_daiLiDGeKB P embedding d hDistance threshold w ell t
      hEll hGridScale hThresholdEll hEdge hLongStrip hSmallStrip hLongCountNat
end QEC.Locality
