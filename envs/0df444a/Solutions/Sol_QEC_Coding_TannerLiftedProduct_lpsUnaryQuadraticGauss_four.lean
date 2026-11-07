-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:52:33.691206+00:00
-- url     : https://prove2.me/submissions/c3384211-f85f-445a-b975-c943fd8d8cd4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFin_cast_finEquiv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticPhase_stdAddChar
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : ℤ) :
    lpsUnaryQuadraticGauss a 4=2+2*ZMod.stdAddChar (a:ZMod 4) := by
  unfold lpsUnaryQuadraticGauss
  simp_rw [lpsQuadraticPhase_stdAddChar]
  rw [Fin.sum_univ_four]
  have hv (r : Fin 4) : ZMod.finEquiv 4 r=(r.val:ZMod 4) := (lpsFin_cast_finEquiv 4 r).symm
  simp only [hv]
  rw [show ((0:Fin 4).val:ZMod 4)^2=0 by decide,
    show ((1:Fin 4).val:ZMod 4)^2=1 by decide,
    show ((2:Fin 4).val:ZMod 4)^2=0 by decide,
    show ((3:Fin 4).val:ZMod 4)^2=1 by decide]
  simp only [mul_zero,mul_one,AddChar.map_zero_eq_one]
  ring
end QEC.Coding.TannerLiftedProduct
