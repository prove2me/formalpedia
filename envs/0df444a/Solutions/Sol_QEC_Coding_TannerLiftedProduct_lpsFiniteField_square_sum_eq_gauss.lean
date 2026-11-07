-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsFiniteField_square_sum_eq_gauss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:52:27.370356+00:00
-- url     : https://prove2.me/submissions/d31a0752-18a9-4839-aa12-0074991d93d1

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
theorem _root_.solution (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F≠2) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    (∑ x : F, ψ (x^2)) =
      gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) ψ := by
  classical
  have hc (y : F) :
      ((Finset.univ.filter (fun x : F => x^2=y)).card:ℂ) =
        ((quadraticChar F y:ℤ):ℂ)+1 := by
    have h := quadraticChar_card_sqrts hF y
    simp only [Set.toFinset_ofPred] at h
    exact_mod_cast h
  rw [← Finset.sum_fiberwise' Finset.univ (fun x : F => x^2) ψ]
  simp only [Finset.sum_const,nsmul_eq_mul,hc,add_mul,one_mul]
  rw [Finset.sum_add_distrib]
  have hn : ψ≠1 := by simpa only [AddChar.mulShift_one] using hψ (one_ne_zero : (1:F)≠0)
  rw [AddChar.sum_eq_zero_of_ne_one hn,add_zero]
  rfl
end QEC.Coding.TannerLiftedProduct
