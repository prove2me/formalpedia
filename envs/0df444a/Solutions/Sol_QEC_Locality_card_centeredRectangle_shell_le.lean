-- Prove2me | solution 1 for QEC.Locality.card_centeredRectangle_shell_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:50:51.290185+00:00
-- url     : https://prove2.me/submissions/2535d7df-5847-4751-861a-790846b046e0

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Theorems.Thm_QEC_Locality_centeredRectangle_shell_subset_shellCover
import Theorems.Thm_QEC_Locality_card_centeredRectangleShellStrip_zero_le
import Theorems.Thm_QEC_Locality_card_centeredRectangleShellStrip_one_le
import Theorems.Thm_QEC_Locality_card_centeredRectangleShellStrip_two_le
import Theorems.Thm_QEC_Locality_card_centeredRectangleShellStrip_three_le

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
attribute [local instance] QEC.Locality.instClassicalDecidableRecursive
namespace QEC.Locality
theorem _root_.solution
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerHorizontalRadius outerVerticalRadius threshold : ℝ)
    (hthreshold : 1 ≤ threshold) (hHorizontal : 1 ≤ 2 * outerHorizontalRadius)
    (hVertical : 1 ≤ 2 * outerVerticalRadius) :
    ((centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius \
        centeredRectangleQubits embedding center (outerHorizontalRadius - threshold)
          (outerVerticalRadius - threshold)).card : ℝ) ≤
      24 * (outerHorizontalRadius + outerVerticalRadius) * threshold := by
  have hsubset := centeredRectangle_shell_subset_shellCover embedding center
    outerHorizontalRadius outerVerticalRadius threshold
  have hcoverNat :
      (centeredRectangleShellCover embedding center outerHorizontalRadius outerVerticalRadius
        threshold).card ≤
        ∑ j : Fin 4,
          (centeredRectangleShellStrips embedding center outerHorizontalRadius
            outerVerticalRadius threshold j).card :=
    Finset.card_biUnion_le
  calc
    _ ≤ ((centeredRectangleShellCover embedding center outerHorizontalRadius outerVerticalRadius
      threshold).card : ℝ) := by exact_mod_cast Finset.card_le_card hsubset
    _ ≤ ∑ j : Fin 4,
        ((centeredRectangleShellStrips embedding center outerHorizontalRadius
          outerVerticalRadius threshold j).card : ℝ) := by exact_mod_cast hcoverNat
    _ ≤ 2 * (12 * outerVerticalRadius * threshold) +
        2 * (12 * outerHorizontalRadius * threshold) := by
      rw [Fin.sum_univ_four]
      nlinarith [card_centeredRectangleShellStrip_zero_le embedding center
        outerHorizontalRadius outerVerticalRadius threshold hthreshold hVertical,
        card_centeredRectangleShellStrip_one_le embedding center
          outerHorizontalRadius outerVerticalRadius threshold hthreshold hVertical,
        card_centeredRectangleShellStrip_two_le embedding center
          outerHorizontalRadius outerVerticalRadius threshold hthreshold hHorizontal,
        card_centeredRectangleShellStrip_three_le embedding center
          outerHorizontalRadius outerVerticalRadius threshold hthreshold hHorizontal]
    _ = _ := by ring
end QEC.Locality
