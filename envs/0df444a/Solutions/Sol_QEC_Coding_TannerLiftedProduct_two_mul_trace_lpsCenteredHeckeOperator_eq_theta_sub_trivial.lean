-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.two_mul_trace_lpsCenteredHeckeOperator_eq_theta_sub_trivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:35:31.562648+00:00
-- url     : https://prove2.me/submissions/237442e9-f8c7-44a7-a1f6-fefd80f2935b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_two_mul_trace_lpsFiniteHeckeElement_eq_card_mul_thetaCoeff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_degree_eq_geomSum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_trace_lpsCenteredHeckeOperator

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ) :
    2 * LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ)
          (lpsCenteredHeckeOperator a n) =
      (Fintype.card PSL(2, ZMod a.q) : ℂ) *
          ((PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) : ℕ) : ℂ) -
        2 * ((∑ i ∈ Finset.range (n + 1), (p : ℂ) ^ i) -
          (lpsHeckePolynomial ℂ (p : ℂ) n).eval 0) := by
  rw [trace_lpsCenteredHeckeOperator]
  calc
    2 * (LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ)
            (cayleyRightRegularRepresentation.asAlgebraHom
              (lpsFiniteHeckeElement a n)) -
          ((lpsHeckePolynomial ℂ (p : ℂ) n).eval ((p : ℂ) + 1) -
            (lpsHeckePolynomial ℂ (p : ℂ) n).eval 0)) =
        2 * LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ)
            (cayleyRightRegularRepresentation.asAlgebraHom
              (lpsFiniteHeckeElement a n)) -
          2 * ((lpsHeckePolynomial ℂ (p : ℂ) n).eval ((p : ℂ) + 1) -
            (lpsHeckePolynomial ℂ (p : ℂ) n).eval 0) := by ring
    _ = (Fintype.card PSL(2, ZMod a.q) : ℂ) *
            ((PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) : ℕ) : ℂ) -
          2 * ((lpsHeckePolynomial ℂ (p : ℂ) n).eval ((p : ℂ) + 1) -
            (lpsHeckePolynomial ℂ (p : ℂ) n).eval 0) := by
      rw [two_mul_trace_lpsFiniteHeckeElement_eq_card_mul_thetaCoeff]
    _ = _ := by rw [lpsHeckePolynomial_eval_degree_eq_geomSum]
end QEC.Coding.TannerLiftedProduct
