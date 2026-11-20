-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationRoot_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:34:48.971503+00:00
-- url     : https://prove2.me/submissions/5fc308f6-10dc-4a21-b8a4-6d4cf7fa71f7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationEquiv_root_coe


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    (lpsOriginalRelativeGaussNormalizationRoot N p hNp h4N hN hpN).val.val =
      lpsOriginalJNInFractionField (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos) :=
  lpsOriginalRelativeGaussNormalizationEquiv_root_coe N p hNp h4N hN hpN
end QEC.Coding.TannerLiftedProduct
