-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_degree_eq_geomSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:01:54.461885+00:00
-- url     : https://prove2.me/submissions/88056bfa-0c8a-41d2-82ad-c59fcd8d2c95

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_add_one_eq_geomSum


set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (p n : ℕ) :
    (lpsHeckePolynomial ℂ (p : ℂ) n).eval ((p : ℂ) + 1) =
      ∑ i ∈ Finset.range (n + 1), (p : ℂ) ^ i := by
  exact lpsHeckePolynomial_eval_add_one_eq_geomSum ℂ (p : ℂ) n
end QEC.Coding.TannerLiftedProduct
