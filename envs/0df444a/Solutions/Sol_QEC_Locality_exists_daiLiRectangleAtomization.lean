-- Prove2me | solution 1 for QEC.Locality.exists_daiLiRectangleAtomization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:21:01.5982+00:00
-- url     : https://prove2.me/submissions/703c5b65-b204-4474-9792-9f29dd250fb3

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Theorems.Thm_QEC_Locality_exists_daiLiHorizontalAtomization

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
    (ell : ℝ) (hEll : 0 < ell)
    (hHeight : 5 * ell ≤ rectangleUpper.2 - rectangleLower.2) :
    ∃ atoms,
      DaiLiHorizontalAtomization
        (daiLiVerticalQubitSupport embedding rectangleLower rectangleUpper)
        ell rectangleLower.2 rectangleUpper.2 atoms := by
  exact exists_daiLiHorizontalAtomization
    (daiLiVerticalQubitSupport embedding rectangleLower rectangleUpper)
    ell rectangleLower.2 rectangleUpper.2 hEll hHeight
end QEC.Locality
