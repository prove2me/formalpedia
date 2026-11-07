-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSigmaCombinationTwelve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:22:49.103219+00:00
-- url     : https://prove2.me/submissions/0643ba99-f5ad-4b41-886e-cf5011d64d5c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSigmaDivisorTwelve

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (n : ℕ) :
    12∣5*ArithmeticFunction.sigma 3 n+7*ArithmeticFunction.sigma 5 n := by
  rw [ArithmeticFunction.sigma_apply,ArithmeticFunction.sigma_apply,
    Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  exact Finset.dvd_sum fun d _=>lpsOriginalSigmaDivisorTwelve d
end QEC.Coding.TannerLiftedProduct
