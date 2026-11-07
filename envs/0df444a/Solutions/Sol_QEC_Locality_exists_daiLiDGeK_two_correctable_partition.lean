-- Prove2me | solution 1 for QEC.Locality.exists_daiLiDGeK_two_correctable_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:39:47.23884+00:00
-- url     : https://prove2.me/submissions/708ea3a5-a442-47c8-a329-be1909f803d9

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
import Theorems.Thm_QEC_Locality_daiLiDGeK_partition_pairwise
import Theorems.Thm_QEC_Locality_daiLiDGeK_partition_cover
import Theorems.Thm_QEC_Locality_daiLiDGeKResidual_subset_separator
import Theorems.Thm_QEC_Locality_card_daiLiDGeKResidual_lt_of_separator_lt
import Theorems.Thm_QEC_Locality_exists_daiLiDGeK_source_case
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sum_daiLiInteractionCounter_eq_two_mul_longInteractionCount
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_finiteSubsystem_subset


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
    (hk : 0 < k) (hd : 0 < (d : ℝ)) (hDGeK : k ≤ d)
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
      ((daiLiDGeKResidualSubsystem P embedding d threshold w ell t).selected.card : ℝ) < k ∧
      (daiLiDGeKResidualSubsystem P embedding d threshold w ell t).selected ⊆
        daiLiDGeKSeparator P embedding threshold w ell t ∧
      Disjoint (daiLiDGeKASubsystem P embedding d threshold w ell t).selected
        (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t).selected ∧
      Disjoint (daiLiDGeKASubsystem P embedding d threshold w ell t).selected
        (daiLiDGeKResidualSubsystem P embedding d threshold w ell t).selected ∧
      Disjoint (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t).selected
        (daiLiDGeKResidualSubsystem P embedding d threshold w ell t).selected ∧
      (daiLiDGeKASubsystem P embedding d threshold w ell t).selected ∪
          (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t).selected ∪
            (daiLiDGeKResidualSubsystem P embedding d threshold w ell t).selected = Finset.univ ∧
      (∃ recoveryA : QuantumChannel
          (daiLiDGeKASubsystem P embedding d threshold w ell t).complementSystem
          (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι)
          (daiLiDGeKASubsystem P embedding d threshold w ell t).complementSystem
          P.semanticCode
          (daiLiDGeKASubsystem P embedding d threshold w ell t).erasureChannelFromRegister
          recoveryA) ∧
      ∃ recoveryB : QuantumChannel
          (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t).complementSystem
          (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι)
          (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t).complementSystem
          P.semanticCode
          (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t).erasureChannelFromRegister
          recoveryB := by
  obtain ⟨t, hSeparator, _hNoBad, hRecoveryA, hRecoveryB⟩ :=
    exists_daiLiDGeK_source_case P embedding d hDistance threshold w ell k hk hd hDGeK hn
      hDistanceDomain hScale hWidth hLongCount hGridScale hThreshold hWidthNat hEllNat
      hThresholdEll hEdge hLongStrip hSmallStrip baseHorizontalRadius baseVerticalRadius steps
      hBaseHorizontal hBaseVerticalGood hBaseVerticalBad hBaseHorizontalDiameter
      hBaseVerticalDiameter hReachHorizontal hReachVerticalGood hReachVerticalBad hGoodBaseCard
      hBoundaryBudget hShortPackingScale
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
  have hEll : 0 < ell := by
    rw [hScale, daiLiPrincipalFourthRootScale]
    apply mul_pos (by norm_num)
    apply Real.rpow_pos_of_pos
    positivity
  have hWidthPos : 0 < w := by linarith
  have hPairwise := daiLiDGeK_partition_pairwise P embedding d threshold w ell t
  have hResidualSubset := daiLiDGeKResidual_subset_separator P embedding d threshold w ell t
    hGlobal hWidthPos hEll
  have hResidualLt := card_daiLiDGeKResidual_lt_of_separator_lt P embedding d threshold w ell k
    t hGlobal hWidthPos hEll hSeparator
  have hTrimmedRecovery := exists_erasureRecovery_of_finiteSubsystem_subset
    (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t)
    (daiLiDGeKBSubsystem P embedding threshold w ell t) Finset.sdiff_subset
    P.semanticCode hRecoveryB
  exact ⟨t, hResidualLt, hResidualSubset, hPairwise.1, hPairwise.2.1,
    hPairwise.2.2, daiLiDGeK_partition_cover P embedding d threshold w ell t,
    hRecoveryA, hTrimmedRecovery⟩
end QEC.Locality
