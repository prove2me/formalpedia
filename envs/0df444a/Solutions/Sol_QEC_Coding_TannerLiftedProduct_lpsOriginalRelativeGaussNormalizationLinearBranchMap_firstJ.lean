-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationLinearBranchMap_firstJ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:38:41.141458+00:00
-- url     : https://prove2.me/submissions/dc35e835-d0a7-4883-b1f9-7861d716effd

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFirstResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondCoordinates
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFiberEquiv_base


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q
      (lpsOriginalRelativeGaussNormalizationFirstJ N p hNp h4N hN hpN) =
      lpsOriginalGaussMaximalResidueJ N hN p q := by
  change (lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
    (Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationFirstJ N p hNp h4N hN hpN))).1 = _
  rw [lpsOriginalRelativeGaussNormalizationFirstJ,
    lpsOriginalRelativeGaussNormalizationFiberEquiv_base]
  rfl
end QEC.Coding.TannerLiftedProduct
