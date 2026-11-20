-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalJ_generated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:00:08.418193+00:00
-- url     : https://prove2.me/submissions/79e388f4-7142-4a04-b09f-bfdd87912bb8

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
    (lpsOriginalIntegerNormalJ N hN).val = lpsOriginalRationalJElement N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  change lpsOriginalIntegerAffineToGenerated N hN
    (AdjoinRoot.of (lpsOriginalIntegerPolynomial N hN) Polynomial.X) = _
  rw [lpsOriginalIntegerAffineToGenerated_base,
    lpsOriginalIntegerBaseToGeneratedField_X_eq_existingJ]
end QEC.Coding.TannerLiftedProduct
