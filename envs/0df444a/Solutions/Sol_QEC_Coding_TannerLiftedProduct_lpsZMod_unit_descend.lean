-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsZMod_unit_descend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:47:53.508197+00:00
-- url     : https://prove2.me/submissions/6a3e2ac1-6dda-450a-be72-102492755cc7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N m : ℕ) [NeZero N] [NeZero m]
    (hm : m ∣ N) (a : ℤ) (ha : IsUnit (a:ZMod N)) : IsUnit (a:ZMod m) := by
  have h := ha.map (ZMod.castHom hm (ZMod m))
  simpa only [map_intCast] using h
end QEC.Coding.TannerLiftedProduct
