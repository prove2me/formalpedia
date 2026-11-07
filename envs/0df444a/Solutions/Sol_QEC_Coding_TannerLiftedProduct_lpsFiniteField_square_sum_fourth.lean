-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsFiniteField_square_sum_fourth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:53:43.926883+00:00
-- url     : https://prove2.me/submissions/eb979794-bc31-4b35-9581-949689d2ed96

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFiniteField_square_sum_eq_gauss
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
theorem _root_.solution (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F≠2) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    (∑ x : F, ψ (x^2))^4 = (Fintype.card F:ℂ)^2 := by
  classical
  let χ := (quadraticChar F).ringHomComp (Int.castRingHom ℂ)
  have hχn : χ≠1 :=
    (MulChar.ringHomComp_ne_one_iff (by exact Int.cast_injective)).mpr (quadraticChar_ne_one hF)
  have hχq : χ.IsQuadratic := (quadraticChar_isQuadratic F).comp _
  have hχsq : χ (-1)^2=(1:ℂ) := by
    have h := congrArg (fun f : MulChar F ℂ => f (-1)) hχq.sq_eq_one
    simpa only [MulChar.pow_apply' χ (show (2:ℕ)≠0 by decide),
      MulChar.one_apply (show IsUnit (-1:F) by simp)] using h
  rw [lpsFiniteField_square_sum_eq_gauss F hF ψ hψ,
    show (4:ℕ)=2*2 by decide,pow_mul,gaussSum_sq hχn hχq hψ,mul_pow,hχsq,one_mul]
end QEC.Coding.TannerLiftedProduct
