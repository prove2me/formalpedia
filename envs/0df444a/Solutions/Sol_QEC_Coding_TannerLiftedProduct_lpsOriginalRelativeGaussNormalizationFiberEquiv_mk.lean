-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFiberEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:32:09.998867+00:00
-- url     : https://prove2.me/submissions/c8b35267-783f-4bca-bb99-220102521b40

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (x : LPSOriginalRelativeGaussHeckeOrder N hN p) :
    lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
      (Ideal.Quotient.mk _
        (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN x)) =
      lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q (Ideal.Quotient.mk _ x) := by
  let e := Ideal.quotientEquiv
    (q.map (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p)))
    (q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN))
    (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)
    (lpsOriginalRelativeGaussNormalizationMaximalMap N p hNp h4N hN hpN q)
  have hm := Ideal.quotientEquiv_mk
    (q.map (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p)))
    (q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN))
    (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)
    (lpsOriginalRelativeGaussNormalizationMaximalMap N p hNp h4N hN hpN q) x
  exact congrArg (lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q)
    ((congrArg e.symm hm).symm.trans (e.symm_apply_apply _))
end QEC.Coding.TannerLiftedProduct
