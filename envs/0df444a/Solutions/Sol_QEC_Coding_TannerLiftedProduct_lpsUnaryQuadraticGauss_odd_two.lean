-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_odd_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:52:52.863892+00:00
-- url     : https://prove2.me/submissions/516b2087-a724-4e9d-9023-54bc49756b75

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
theorem _root_.solution (a : ℤ) (ha : Odd a) :
    lpsUnaryQuadraticGauss a 2=0 := by
  unfold lpsUnaryQuadraticGauss
  simp_rw [lpsQuadraticPhase_stdAddChar]
  rw [Fin.sum_univ_two]
  have he : (a:ZMod 2)=1 := by
    obtain ⟨k,hk⟩ := ha
    rw [hk]
    push_cast
    have hz : (2:ZMod 2)=0 := by decide
    linear_combination (k:ZMod 2)*hz
  have hchar : ZMod.stdAddChar (1:ZMod 2)= -1 := by
    have h := ZMod.stdAddChar_coe (N:=2) (1:ℤ)
    norm_num only [Int.cast_one,Nat.cast_ofNat,mul_one] at h
    rw [show (2:ℂ)*Real.pi*Complex.I/2=(Real.pi:ℂ)*Complex.I by ring] at h
    exact h.trans Complex.exp_pi_mul_I
  have hv (r : Fin 2) : ZMod.finEquiv 2 r=(r.val:ZMod 2) := (lpsFin_cast_finEquiv 2 r).symm
  simp only [hv]
  rw [show ((0:Fin 2).val:ZMod 2)^2=0 by decide,
    show ((1:Fin 2).val:ZMod 2)^2=1 by decide]
  simp only [mul_zero,mul_one,he,AddChar.map_zero_eq_one,hchar,add_neg_cancel]
end QEC.Coding.TannerLiftedProduct
