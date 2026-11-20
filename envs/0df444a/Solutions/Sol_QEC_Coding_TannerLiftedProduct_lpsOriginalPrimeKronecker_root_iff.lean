-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeKronecker_root_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:05:25.82038+00:00
-- url     : https://prove2.me/submissions/33e7c96f-66c0-453a-9eea-6ca71d7da438

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeKronecker_eval

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A] [IsDomain A]
    [Algebra (ZMod p) A] (j y : A) :
    ((lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))).eval₂
      (Polynomial.eval₂RingHom (algebraMap (ZMod p) A) j) y = 0 ↔
      y=j^p ∨ y^p=j := by
  rw [lpsOriginalPrimeKronecker_eval,mul_eq_zero,sub_eq_zero,sub_eq_zero]
end QEC.Coding.TannerLiftedProduct
