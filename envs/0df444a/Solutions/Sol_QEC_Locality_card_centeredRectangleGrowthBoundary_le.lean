-- Prove2me | solution 1 for QEC.Locality.card_centeredRectangleGrowthBoundary_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:53:08.071842+00:00
-- url     : https://prove2.me/submissions/d9deafe3-eb19-4287-8828-7cd1ea08ff79

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Theorems.Thm_QEC_Locality_card_longOutsideNeighborsOf_le_sum_counter
import Theorems.Thm_QEC_Locality_card_centeredRectangle_shell_le

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
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerHorizontalRadius outerVerticalRadius threshold : ℝ)
    (hthreshold : 1 ≤ threshold) (hHorizontal : 1 ≤ 2 * outerHorizontalRadius)
    (hVertical : 1 ≤ 2 * outerVerticalRadius) :
    ((centeredRectangleGrowthBoundary P embedding center outerHorizontalRadius
      outerVerticalRadius threshold).selected.card : ℝ) ≤
      24 * (outerHorizontalRadius + outerVerticalRadius) * threshold +
        ((∑ q ∈ centeredRectangleQubits embedding center
          (outerHorizontalRadius - threshold) (outerVerticalRadius - threshold),
          P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) := by
  let shell := centeredRectangleQubits embedding center outerHorizontalRadius
    outerVerticalRadius \ centeredRectangleQubits embedding center
      (outerHorizontalRadius - threshold) (outerVerticalRadius - threshold)
  let outside := longOutsideNeighborsOf P embedding threshold
    (centeredRectangleQubits embedding center
      (outerHorizontalRadius - threshold) (outerVerticalRadius - threshold))
  have hUnionNat : (shell ∪ outside).card ≤ shell.card + outside.card :=
    Finset.card_union_le shell outside
  have hOutside := card_longOutsideNeighborsOf_le_sum_counter P embedding threshold
    (centeredRectangleQubits embedding center
      (outerHorizontalRadius - threshold) (outerVerticalRadius - threshold))
  calc
    _ ≤ (shell.card : ℝ) + (outside.card : ℝ) := by exact_mod_cast hUnionNat
    _ ≤ 24 * (outerHorizontalRadius + outerVerticalRadius) * threshold +
        ((∑ q ∈ centeredRectangleQubits embedding center
          (outerHorizontalRadius - threshold) (outerVerticalRadius - threshold),
          P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) := by
      gcongr
      exact card_centeredRectangle_shell_le embedding center outerHorizontalRadius
        outerVerticalRadius threshold hthreshold hHorizontal hVertical
end QEC.Locality
