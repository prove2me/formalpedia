-- Prove2me | solution 1 for QEC.Locality.centeredRectangleSubsystem_subset_inner_union_generalGrowthBoundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:40:00.278488+00:00
-- url     : https://prove2.me/submissions/d31b342e-4c4c-4552-af5c-5c3b4b41b665

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition

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
    (innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold : ℝ) :
    (centeredRectangleSubsystem embedding center outerHorizontalRadius
      outerVerticalRadius).selected ⊆
      (unionSubsystem
        (centeredRectangleSubsystem embedding center innerHorizontalRadius innerVerticalRadius)
        (centeredRectangleGeneralGrowthBoundary P embedding center
          innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
          outerVerticalRadius threshold)).selected := by
  intro q hq
  by_cases hqInner : q ∈ centeredRectangleQubits embedding center
      innerHorizontalRadius innerVerticalRadius
  · exact Finset.mem_union_left _ hqInner
  · apply Finset.mem_union_right
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_sdiff.mpr ⟨hq, hqInner⟩))
end QEC.Locality
