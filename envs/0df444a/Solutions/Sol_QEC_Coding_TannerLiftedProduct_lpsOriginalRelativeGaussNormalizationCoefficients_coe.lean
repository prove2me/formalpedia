-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationCoefficients_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:33:32.461584+00:00
-- url     : https://prove2.me/submissions/ecbfa0a3-ecf8-491a-8647-7a99ada039a1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationEquiv_base_coe


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (c : LPSOriginalGaussAffineOrder N hN p) :
    (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN c).val.val =
      (lpsOriginalGaussAffineToGenerated N hN p c).val :=
  lpsOriginalRelativeGaussNormalizationEquiv_base_coe N p hNp h4N hN hpN c
end QEC.Coding.TannerLiftedProduct
