-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFiberEquiv_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:34:58.476154+00:00
-- url     : https://prove2.me/submissions/286f0bb9-acab-409f-a7f4-4f4e3dd4b52d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFiberEquiv_mk

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (c : LPSOriginalGaussAffineOrder N hN p) :
    lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
      (Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN c)) =
      (Ideal.Quotient.mk q c,
        AdjoinRoot.of ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
          Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)) (Ideal.Quotient.mk q c)) := by
  change lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
    (Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN
      (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p) c))) = _
  rw [lpsOriginalRelativeGaussNormalizationFiberEquiv_mk N p hNp h4N hN hpN q]
  exact lpsOriginalRelativeGaussHeckeFiberEquiv_base N hN p hpN q c
end QEC.Coding.TannerLiftedProduct
