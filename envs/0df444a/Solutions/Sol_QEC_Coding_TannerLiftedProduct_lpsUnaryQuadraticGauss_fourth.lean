-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_fourth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:02:10.292917+00:00
-- url     : https://prove2.me/submissions/cf4c874a-2d0f-43bb-932b-1c190534d53d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_fourth_classified
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
theorem _root_.solution (N : ℕ) (hN : 4 ∣ N) (a : ℤ)
    (ha : IsUnit (a:ZMod N)) :
    lpsUnaryQuadraticGauss a N^4= -4*(N:ℂ)^2 := by
  have h := lpsUnaryQuadraticGauss_fourth_classified N a ha
  have hd2 : 2 ∣ N := dvd_trans (show 2 ∣ 4 by decide) hN
  simpa only [lpsGaussFourthFactor,Nat.mod_eq_zero_of_dvd hd2,
    Nat.mod_eq_zero_of_dvd hN,if_neg (by decide : ¬ (0:ℕ)=1),ite_true,
    Int.cast_neg,Int.cast_ofNat] using h
end QEC.Coding.TannerLiftedProduct
