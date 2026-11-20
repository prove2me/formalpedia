-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalZeroToGaussAffineOrder_J
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:03:38.534668+00:00
-- url     : https://prove2.me/submissions/62f8a672-3171-4db2-8a32-fe9e678b169a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalJ_generated

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    lpsOriginalIntegerNormalZeroToGaussAffineOrder N hN p hpN
      (lpsOriginalIntegerNormalJ N hN) =
      AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
  let : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    ((lpsOriginalGaussAffineToGenerated N hN p).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))).toAlgebra
  let e := lpsOriginalGaussNormalizationEquiv N hN p hpN
  apply e.injective
  change e (e.symm ((lpsOriginalIntegerNormalZeroToGaussNormalization N hN p)
    (lpsOriginalIntegerNormalJ N hN))) = e (algebraMap _ _ _)
  erw [e.apply_symm_apply,e.commutes]
  apply Subtype.ext
  change (lpsOriginalIntegerNormalJ N hN).val =
    lpsOriginalGaussBaseToGeneratedField N hN p
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)
  rw [lpsOriginalIntegerNormalJ_generated,lpsOriginalGaussBaseToGeneratedField_base,
    lpsOriginalIntegerBaseToGeneratedField_X_eq_existingJ]
end QEC.Coding.TannerLiftedProduct
