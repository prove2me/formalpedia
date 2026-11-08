-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.trace_lpsCenteredEuclideanHeckeOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:04:26.061731+00:00
-- url     : https://prove2.me/submissions/339cc3dc-c3cd-4f94-9b01-7f09fd5c9276

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCenteredEuclideanHeckeOperator_eq_conj

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ PSL(2, ZMod a.q))
        (lpsCenteredEuclideanHeckeOperator a n) =
      LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ)
        (lpsCenteredHeckeOperator a n) := by
  rw [lpsCenteredEuclideanHeckeOperator_eq_conj,
    LinearMap.trace_conj']
end QEC.Coding.TannerLiftedProduct
