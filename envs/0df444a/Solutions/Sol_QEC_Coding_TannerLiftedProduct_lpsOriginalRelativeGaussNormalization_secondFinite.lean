-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalization_secondFinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:47:06.85438+00:00
-- url     : https://prove2.me/submissions/841b6b71-d83c-44fd-854a-2c3b27a2e9dc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondResidueDegrees
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFricke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFrickePullback_comp_first
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalization_firstFinite

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
    Module.Finite (LPSOriginalGaussAffineOrder N hN p)
      (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := by
  let R := LPSOriginalGaussAffineOrder N hN p
  let C := LPSOriginalRelativeGaussNormalization N p hNp h4N hN
  let := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
  refine @Module.Finite.of_equiv_equiv R C R C _ _ _ _
    (lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN)
    (lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN)
    (lpsOriginalGaussFrickeRingEquiv N hN p hpN)
    (lpsOriginalRelativeGaussNormalizationFrickeRingEquiv N p hNp h4N hN hpN)
    ?_ (lpsOriginalRelativeGaussNormalization_firstFinite N p hNp h4N hN hpN)
  exact (lpsOriginalRelativeGaussNormalizationFrickePullback_comp_first N p hNp h4N hN hpN).symm
end QEC.Coding.TannerLiftedProduct
