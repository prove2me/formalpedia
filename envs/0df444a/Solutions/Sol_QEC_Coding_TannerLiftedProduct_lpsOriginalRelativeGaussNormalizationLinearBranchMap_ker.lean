-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationLinearBranchMap_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:02:29.411684+00:00
-- url     : https://prove2.me/submissions/66d89c60-74eb-4f04-9ee6-b07255a35a55

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusDescent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMapKernelCompositionEquiv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationLinearBranchMap_comp_equiv

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    RingHom.ker (lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q) =
      LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q := by
  change RingHom.ker (lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q) =
    (RingHom.ker (lpsOriginalRelativeGaussHeckeLinearBranchMap N hN p hpN q)).map
      (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)
  rw [← lpsOriginalRelativeGaussNormalizationLinearBranchMap_comp_equiv N p hNp h4N hN hpN q]
  exact (lpsOriginalMapKernelCompositionEquiv
    (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)
    (lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q)).symm
end QEC.Coding.TannerLiftedProduct
