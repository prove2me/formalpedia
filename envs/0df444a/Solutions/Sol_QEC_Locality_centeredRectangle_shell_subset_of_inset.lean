-- Prove2me | solution 1 for QEC.Locality.centeredRectangle_shell_subset_of_inset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:39:55.209771+00:00
-- url     : https://prove2.me/submissions/00029c84-f0c0-4bf7-bd54-390dcacf44c6

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Theorems.Thm_QEC_Locality_centeredRectangleQubits_subset_of_radii_le

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
    (innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold : ℝ)
    (hHorizontalInner : outerHorizontalRadius - threshold ≤ innerHorizontalRadius)
    (hVerticalInner : outerVerticalRadius - threshold ≤ innerVerticalRadius) :
    centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius \
        centeredRectangleQubits embedding center innerHorizontalRadius innerVerticalRadius ⊆
      centeredRectangleQubits embedding center outerHorizontalRadius outerVerticalRadius \
        centeredRectangleQubits embedding center (outerHorizontalRadius - threshold)
          (outerVerticalRadius - threshold) := by
  intro q hq
  refine Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hq).1, ?_⟩
  intro hqDeep
  exact (Finset.mem_sdiff.mp hq).2
    (centeredRectangleQubits_subset_of_radii_le embedding center
      hHorizontalInner hVerticalInner hqDeep)
end QEC.Locality
