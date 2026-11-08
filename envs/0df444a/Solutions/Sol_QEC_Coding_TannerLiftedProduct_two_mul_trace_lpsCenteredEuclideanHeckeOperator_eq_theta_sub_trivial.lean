-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.two_mul_trace_lpsCenteredEuclideanHeckeOperator_eq_theta_sub_trivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:42:05.395192+00:00
-- url     : https://prove2.me/submissions/3a057836-a476-40b3-8629-131d177c26b4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_trace_lpsCenteredEuclideanHeckeOperator
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_two_mul_trace_lpsCenteredHeckeOperator_eq_theta_sub_trivial

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ) :
    2 * LinearMap.trace ℂ (EuclideanSpace ℂ PSL(2, ZMod a.q))
          (lpsCenteredEuclideanHeckeOperator a n) =
      (Fintype.card PSL(2, ZMod a.q) : ℂ) *
          ((PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) : ℕ) : ℂ) -
        2 * ((∑ i ∈ Finset.range (n + 1), (p : ℂ) ^ i) -
          (lpsHeckePolynomial ℂ (p : ℂ) n).eval 0) := by
  rw [trace_lpsCenteredEuclideanHeckeOperator,
    two_mul_trace_lpsCenteredHeckeOperator_eq_theta_sub_trivial]
end QEC.Coding.TannerLiftedProduct
