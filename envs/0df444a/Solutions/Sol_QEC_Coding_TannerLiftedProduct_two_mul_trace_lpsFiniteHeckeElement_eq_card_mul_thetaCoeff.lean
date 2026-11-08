-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.two_mul_trace_lpsFiniteHeckeElement_eq_card_mul_thetaCoeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:32:56.863768+00:00
-- url     : https://prove2.me/submissions/e7e04ed8-d833-4e7a-a160-8a862fde957c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_heckeCoeff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_trace_lpsFiniteHeckeElement


set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ) :
    2 * LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ)
          (cayleyRightRegularRepresentation.asAlgebraHom
            (lpsFiniteHeckeElement a n)) =
      (Fintype.card PSL(2, ZMod a.q) : ℂ) *
        ((PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) : ℕ) : ℂ) := by
  rw [trace_lpsFiniteHeckeElement,
    coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_heckeCoeff]
  ring
end QEC.Coding.TannerLiftedProduct
