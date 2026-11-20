-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussAffineToGenerated_j
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:15:36.188323+00:00
-- url     : https://prove2.me/submissions/05bef65c-1cc4-47e6-b189-a10565899d65

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGaussAffineToGenerated N hN p
      (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X))).val =
      lpsOriginalJInFractionField := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  change (lpsOriginalGaussBaseToGeneratedField N hN p
    (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)).val = _
  rw [lpsOriginalGaussBaseToGeneratedField_base]
  exact lpsOriginalIntegerBaseToGeneratedField_X_coe N hN
end QEC.Coding.TannerLiftedProduct
