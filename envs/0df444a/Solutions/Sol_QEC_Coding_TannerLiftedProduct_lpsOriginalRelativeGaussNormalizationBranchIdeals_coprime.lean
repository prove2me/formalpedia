-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationBranchIdeals_coprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:39:18.554062+00:00
-- url     : https://prove2.me/submissions/5626a725-0927-4253-b9e2-3b38402614f9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussHeckeBranchIdeals_coprime


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] : IsCoprime (LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q) (LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  change ((LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q).map
      (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)) ⊔ ((LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q).map
      (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)) = ⊤
  rw [← Ideal.map_sup,(lpsOriginalRelativeGaussHeckeBranchIdeals_coprime N hN p hpN q).sup_eq,
    Ideal.map_top]
end QEC.Coding.TannerLiftedProduct
