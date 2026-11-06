-- Prove2me | solution 1 for QEC.Locality.daiLi_halfOpenHorizontalCut_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:04:30.582495+00:00
-- url     : https://prove2.me/submissions/672e8cbf-b223-4a51-a7ba-e5f23fe7363e

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution
    (embedding : UnitSeparatedEmbedding2D ι) (rectangleLower rectangleUpper : ℝ × ℝ)
    (cut : ℝ) :
    Disjoint (daiLiBelowHorizontalCut embedding rectangleLower rectangleUpper cut)
      (daiLiAtOrAboveHorizontalCut embedding rectangleLower rectangleUpper cut) := by
  apply Finset.disjoint_left.mpr
  intro q hBelow hAbove
  exact (not_lt_of_ge (Finset.mem_filter.mp hAbove).2) (Finset.mem_filter.mp hBelow).2
end QEC.Locality
