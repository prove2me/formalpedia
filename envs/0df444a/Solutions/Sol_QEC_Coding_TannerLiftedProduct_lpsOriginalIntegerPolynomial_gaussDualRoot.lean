-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_gaussDualRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:14:20.737207+00:00
-- url     : https://prove2.me/submissions/1596cf44-38d0-4150-b28b-1099b2fea848

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_normalDualRoot_image
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalZeroToGaussAffineOrder_JN
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalZeroToGaussAffineOrder_J

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    (lpsOriginalIntegerPolynomial N hN).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom _)
        (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)))
      (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)) = 0 := by
  have h := lpsOriginalIntegerPolynomial_normalDualRoot_image N hN
    (LPSOriginalGaussAffineOrder N hN p)
    (lpsOriginalIntegerNormalZeroToGaussAffineOrder N hN p hpN)
  rw [lpsOriginalIntegerNormalZeroToGaussAffineOrder_JN,
    lpsOriginalIntegerNormalZeroToGaussAffineOrder_J] at h
  exact h
end QEC.Coding.TannerLiftedProduct
