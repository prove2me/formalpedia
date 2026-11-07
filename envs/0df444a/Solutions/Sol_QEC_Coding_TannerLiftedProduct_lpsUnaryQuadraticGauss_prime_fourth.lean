-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_prime_fourth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:54:36.687986+00:00
-- url     : https://prove2.me/submissions/88a2514e-b00f-4cf8-a81e-6ceda5e34097

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFiniteField_square_sum_fourth
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticFourier_zero_eq_Gauss
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime]
    (hp2 : p≠2) (a : ℤ) (ha : (a:ZMod p)≠0) :
    lpsUnaryQuadraticGauss a p^4 = (p:ℂ)^2 := by
  let ψ := (ZMod.stdAddChar (N:=p)).mulShift (a:ZMod p)
  have hψn : ψ≠1 := ZMod.isPrimitive_stdAddChar p ha
  have hψ : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one hψn
  have hF : ringChar (ZMod p)≠2 := by rw [ZMod.ringChar_zmod_n];exact hp2
  have h := lpsFiniteField_square_sum_fourth (ZMod p) hF ψ hψ
  rw [ZMod.card] at h
  have hg : lpsUnaryQuadraticGauss a p=(∑ x : ZMod p, ψ (x^2)) := by
    rw [← lpsQuadraticFourier_zero_eq_Gauss,lpsQuadraticFourier]
    simp only [zero_mul,add_zero,ψ,AddChar.mulShift_apply]
  rw [hg]
  exact h
end QEC.Coding.TannerLiftedProduct
