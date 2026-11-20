-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_productLevelFractionRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:09:03.355919+00:00
-- url     : https://prove2.me/submissions/4d947903-4ca5-452c-b95e-ca47f3e03118

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_productLevelHolomorphicRoot

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero p] (hN : 0 < N) (hp : 0 < p) :
    (lpsOriginalIntegerPolynomial p hp).eval₂ (lpsOriginalJNIntegerFractionEval N hN)
      (lpsOriginalJNInFractionField (N*p) (Nat.mul_pos hN hp)) = 0 := by
  have he := Polynomial.hom_eval₂ (lpsOriginalIntegerPolynomial p hp)
    (lpsOriginalJNHolomorphicEvalZ N hN)
    (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField)
    (lpsOriginalJNHolomorphic (N*p) (Nat.mul_pos hN hp))
  change (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField)
    ((lpsOriginalIntegerPolynomial p hp).eval₂ (lpsOriginalJNHolomorphicEvalZ N hN)
      (lpsOriginalJNHolomorphic (N*p) (Nat.mul_pos hN hp))) = _ at he
  rw [lpsOriginalPrimeIntegerPolynomial_productLevelHolomorphicRoot,map_zero] at he
  exact he.symm
end QEC.Coding.TannerLiftedProduct
