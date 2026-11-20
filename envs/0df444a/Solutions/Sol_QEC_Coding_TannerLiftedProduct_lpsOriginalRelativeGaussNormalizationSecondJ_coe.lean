-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationSecondJ_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:37:49.987461+00:00
-- url     : https://prove2.me/submissions/eb039658-bba5-40b6-b889-7ab4e7821479

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondCoordinates

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN).val.val =
      lpsOriginalJNInFractionField p (Fact.out : p.Prime).pos :=
  lpsOriginalRelativeGaussSecondJField_coe N p h4N hN (Fact.out : p.Prime).pos
end QEC.Coding.TannerLiftedProduct
