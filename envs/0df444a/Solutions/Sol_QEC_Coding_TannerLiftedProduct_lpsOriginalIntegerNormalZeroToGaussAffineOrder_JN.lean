-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalZeroToGaussAffineOrder_JN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:05:29.323018+00:00
-- url     : https://prove2.me/submissions/05339da8-179d-42da-92b9-8a589208c1b8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalJN_generated
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussNormalizationEquiv_root


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    lpsOriginalIntegerNormalZeroToGaussAffineOrder N hN p hpN
      (lpsOriginalIntegerNormalJN N hN) =
      AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
  let : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    ((lpsOriginalGaussAffineToGenerated N hN p).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))).toAlgebra
  let e := lpsOriginalGaussNormalizationEquiv N hN p hpN
  apply e.injective
  change e (e.symm ((lpsOriginalIntegerNormalZeroToGaussNormalization N hN p)
    (lpsOriginalIntegerNormalJN N hN))) = e _
  erw [e.apply_symm_apply]
  apply Subtype.ext
  apply Subtype.ext
  change (lpsOriginalIntegerNormalJN N hN).val.val =
    (e (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p))).val.val
  rw [lpsOriginalIntegerNormalJN_generated,lpsOriginalRationalJNElement_coe,
    lpsOriginalGaussNormalizationEquiv_root]
end QEC.Coding.TannerLiftedProduct
