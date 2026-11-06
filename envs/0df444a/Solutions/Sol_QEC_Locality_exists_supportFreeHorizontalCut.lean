-- Prove2me | solution 1 for QEC.Locality.exists_supportFreeHorizontalCut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:20:11.191283+00:00
-- url     : https://prove2.me/submissions/98c37b39-20a4-4164-9148-45c7a2c7e43d

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Theorems.Thm_QEC_Locality_exists_real_in_openInterval_not_mem_finset

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
    {lower upper : ℝ} (hInterval : lower < upper) :
    ∃ cut : ℝ, lower < cut ∧ cut < upper ∧
      ∀ q ∈ embedding.qubitsInRectangle rectangleLower rectangleUpper,
        (embedding.point q).2 ≠ cut := by
  rcases exists_real_in_openInterval_not_mem_finset
      (daiLiVerticalQubitSupport embedding rectangleLower rectangleUpper) hInterval with
    ⟨cut, hLower, hUpper, hCut⟩
  refine ⟨cut, hLower, hUpper, ?_⟩
  intro q hq hqCut
  apply hCut
  exact Finset.mem_image.mpr ⟨q, hq, hqCut⟩
end QEC.Locality
