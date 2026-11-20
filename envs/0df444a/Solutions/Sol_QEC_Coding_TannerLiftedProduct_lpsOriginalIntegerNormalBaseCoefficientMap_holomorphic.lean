-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalBaseCoefficientMap_holomorphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:01:04.037838+00:00
-- url     : https://prove2.me/submissions/501a2044-2bc2-4035-ae01-f3afc52905cf

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionEmbeddingQ_polynomial


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalIntegerNormalToHolomorphic N hN).comp
      (lpsOriginalIntegerNormalBaseCoefficientMap N hN) =
      (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField).comp
        lpsOriginalJHolomorphicEvalZ := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  apply RingHom.ext
  intro f
  change ((lpsOriginalIntegerAffineToGenerated N hN
    (AdjoinRoot.of (lpsOriginalIntegerPolynomial N hN) f)) :
      LPSOriginalHolomorphicFractionField) = _
  rw [lpsOriginalIntegerAffineToGenerated_base]
  change lpsOriginalJFractionEmbeddingQ (lpsOriginalIntegerBaseFractionMap f) = _
  rw [lpsOriginalIntegerBaseFractionMap, RingHom.comp_apply, Polynomial.coe_mapRingHom,
    lpsOriginalJFractionEmbeddingQ_polynomial]
  rfl
end QEC.Coding.TannerLiftedProduct
