-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalJN_generated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:00:38.831469+00:00
-- url     : https://prove2.me/submissions/fe6d6d1c-2f42-444c-9bb0-569c5ffc1ecc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalIntegerNormalJN N hN).val = lpsOriginalRationalJNElement N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  rfl
end QEC.Coding.TannerLiftedProduct
