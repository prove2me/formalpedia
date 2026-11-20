-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_productLevelNormalRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:15:06.239846+00:00
-- url     : https://prove2.me/submissions/cdcec034-8112-4209-a930-7e54277bb739

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_productLevelFractionRoot
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalToHolomorphic_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalToHolomorphic_JN
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProductLevelCoefficientMap_holomorphic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)]
    (h4N : 4 ∣ N) (hN : 0 < N) (hp : 0 < p) :
    (lpsOriginalIntegerPolynomial p hp).eval₂
      (lpsOriginalIntegerProductLevelCoefficientMap N p h4N hN hp)
      (lpsOriginalIntegerNormalJN (N*p) (Nat.mul_pos hN hp)) = 0 := by
  apply lpsOriginalIntegerNormalToHolomorphic_injective (N*p) (Nat.mul_pos hN hp)
  rw [map_zero, Polynomial.hom_eval₂,
    lpsOriginalIntegerProductLevelCoefficientMap_holomorphic,
    lpsOriginalIntegerNormalToHolomorphic_JN,
    lpsOriginalPrimeIntegerPolynomial_productLevelFractionRoot]
end QEC.Coding.TannerLiftedProduct
