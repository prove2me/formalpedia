-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationBranchIdeals_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:44:59.734217+00:00
-- url     : https://prove2.me/submissions/2590271c-fd0a-4709-970e-0012bde3cfdc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussHeckeBranchIdeals_product


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q) * (LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) = q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN) := by
  change ((LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q).map
      (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)) * ((LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q).map
      (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)) = _
  rw [← Ideal.map_mul,lpsOriginalRelativeGaussHeckeBranchIdeals_product N hN p hpN q]
  exact (lpsOriginalRelativeGaussNormalizationMaximalMap N p hNp h4N hN hpN q).symm
end QEC.Coding.TannerLiftedProduct
