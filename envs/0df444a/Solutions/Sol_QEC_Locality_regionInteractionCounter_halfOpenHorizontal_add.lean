-- Prove2me | solution 1 for QEC.Locality.regionInteractionCounter_halfOpenHorizontal_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:46:27.209575+00:00
-- url     : https://prove2.me/submissions/efd0be12-3d10-4109-8d27-4d7b1a345177

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Theorems.Thm_QEC_Locality_daiLi_halfOpenHorizontalCut_disjoint
import Theorems.Thm_QEC_Locality_daiLi_halfOpenHorizontalCut_union

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
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (rectangleLower rectangleUpper : ℝ × ℝ) (cut : ℝ) :
    regionInteractionCounter P embedding threshold
        (daiLiBelowHorizontalCut embedding rectangleLower rectangleUpper cut) +
      regionInteractionCounter P embedding threshold
        (daiLiAtOrAboveHorizontalCut embedding rectangleLower rectangleUpper cut) =
      regionInteractionCounter P embedding threshold
        (embedding.qubitsInRectangle rectangleLower rectangleUpper) := by
  unfold regionInteractionCounter
  rw [← Finset.sum_union
    (daiLi_halfOpenHorizontalCut_disjoint embedding rectangleLower rectangleUpper cut),
    daiLi_halfOpenHorizontalCut_union]
end QEC.Locality
