-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFiberEquiv_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:35:01.742468+00:00
-- url     : https://prove2.me/submissions/70b15db7-af36-4b81-aaaf-c9269daae40b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFiberEquiv_mk
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussHeckeFiberEquiv_root


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
      (Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationRoot N p hNp h4N hN hpN)) =
      ((lpsOriginalGaussMaximalResidueJN N hN p q)^p,
        AdjoinRoot.root ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
          Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))) := by
  change lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
    (Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN
      (AdjoinRoot.root (lpsOriginalRelativeGaussHeckePolynomial N hN p)))) = _
  rw [lpsOriginalRelativeGaussNormalizationFiberEquiv_mk N p hNp h4N hN hpN q]
  exact lpsOriginalRelativeGaussHeckeFiberEquiv_root N hN p hpN q
end QEC.Coding.TannerLiftedProduct
