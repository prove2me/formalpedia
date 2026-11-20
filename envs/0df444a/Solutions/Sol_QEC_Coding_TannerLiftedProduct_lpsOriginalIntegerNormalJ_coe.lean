-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalJ_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:03:41.86041+00:00
-- url     : https://prove2.me/submissions/81525bbd-3d62-4624-bcb3-8110db67bce1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalJ_generated

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalToHolomorphic N hN (lpsOriginalIntegerNormalJ N hN) =
      lpsOriginalJInFractionField := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  change (lpsOriginalIntegerNormalJ N hN).val.val = _
  rw [lpsOriginalIntegerNormalJ_generated,lpsOriginalRationalJElement_coe]
end QEC.Coding.TannerLiftedProduct
