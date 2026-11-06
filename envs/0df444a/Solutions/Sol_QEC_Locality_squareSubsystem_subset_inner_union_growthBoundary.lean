-- Prove2me | solution 1 for QEC.Locality.squareSubsystem_subset_inner_union_growthBoundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:38:44.799393+00:00
-- url     : https://prove2.me/submissions/8c94c772-bc52-4a79-b65a-1f487fe0d4f7

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
    (outerRadius threshold : ℝ) :
    (squareSubsystem embedding center outerRadius).selected ⊆
      (unionSubsystem
        (squareSubsystem embedding center (outerRadius - threshold))
        (squareGrowthBoundary P embedding center outerRadius threshold)).selected := by
  intro q hq
  by_cases hqInner : q ∈ squareQubits embedding center (outerRadius - threshold)
  · exact Finset.mem_union_left _ hqInner
  · apply Finset.mem_union_right
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hq, hqInner⟩)
end QEC.Locality
