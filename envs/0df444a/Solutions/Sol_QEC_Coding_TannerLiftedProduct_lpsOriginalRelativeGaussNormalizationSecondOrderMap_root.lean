-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationSecondOrderMap_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:15:03.393794+00:00
-- url     : https://prove2.me/submissions/cd9f5dce-16cd-4d36-8b96-61b9f5f38d7e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN
      (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)) =
      lpsOriginalRelativeGaussNormalizationRoot N p hNp h4N hN hpN :=
  AdjoinRoot.lift_root _
end QEC.Coding.TannerLiftedProduct
