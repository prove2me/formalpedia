-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:52:39.067564+00:00
-- url     : https://prove2.me/submissions/a144bfd4-08e0-4f19-9fae-b931dc3d9892

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChar_eight_four
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
theorem _root_.solution (a : ℤ) (ha : Odd a) :
    lpsUnaryQuadraticGauss a 8=4*ZMod.stdAddChar (a:ZMod 8) := by
  unfold lpsUnaryQuadraticGauss
  simp_rw [lpsQuadraticPhase_stdAddChar]
  rw [Fin.sum_univ_eight]
  have hv (r : Fin 8) : ZMod.finEquiv 8 r=(r.val:ZMod 8) := (lpsFin_cast_finEquiv 8 r).symm
  simp only [hv]
  rw [show ((0:Fin 8).val:ZMod 8)^2=0 by decide,
    show ((1:Fin 8).val:ZMod 8)^2=1 by decide,
    show ((2:Fin 8).val:ZMod 8)^2=4 by decide,
    show ((3:Fin 8).val:ZMod 8)^2=1 by decide,
    show ((4:Fin 8).val:ZMod 8)^2=0 by decide,
    show ((5:Fin 8).val:ZMod 8)^2=1 by decide,
    show ((6:Fin 8).val:ZMod 8)^2=4 by decide,
    show ((7:Fin 8).val:ZMod 8)^2=1 by decide]
  have he : (a:ZMod 8)*4=4 := by
    obtain ⟨k,hk⟩ := ha
    rw [hk]
    push_cast
    have hz : (8:ZMod 8)=0 := by decide
    linear_combination (k:ZMod 8)*hz
  simp only [mul_zero,mul_one,AddChar.map_zero_eq_one,he,lpsChar_eight_four]
  ring
end QEC.Coding.TannerLiftedProduct
