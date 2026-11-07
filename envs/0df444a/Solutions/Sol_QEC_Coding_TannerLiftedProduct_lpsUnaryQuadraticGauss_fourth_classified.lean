-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_fourth_classified
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:00:56.555124+00:00
-- url     : https://prove2.me/submissions/a188b729-552a-4cd6-a4e7-882fb77ea3b6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_coprime_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsZMod_unit_descend
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGaussFourthFactor_coprime_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGaussFourthFactor_prime_pow
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
theorem _root_.solution (N : ℕ) (a : ℤ)
    (ha : IsUnit (a:ZMod N)) :
    lpsUnaryQuadraticGauss a N^4=(lpsGaussFourthFactor N:ℂ)*(N:ℂ)^2 := by
  induction N using Nat.recOnPrimeCoprime generalizing a with
  | zero => simp [lpsUnaryQuadraticGauss,lpsGaussFourthFactor]
  | prime_pow p e hp => exact lpsGaussFourthFactor_prime_pow p e hp a ha
  | coprime m n hm hn hcop ihm ihn =>
    let : NeZero m := ⟨by omega⟩
    let : NeZero n := ⟨by omega⟩
    have haM := lpsZMod_unit_descend (m*n) m (Nat.dvd_mul_right _ _) a ha
    have haN := lpsZMod_unit_descend (m*n) n (Nat.dvd_mul_left _ _) a ha
    have hum : IsUnit (((a*(n:ℤ):ℤ):ZMod m)) := by
      simpa only [Int.cast_mul,Int.cast_natCast] using
        haM.mul ((ZMod.isUnit_iff_coprime n m).mpr hcop.symm)
    have hun : IsUnit (((a*(m:ℤ):ℤ):ZMod n)) := by
      simpa only [Int.cast_mul,Int.cast_natCast] using
        haN.mul ((ZMod.isUnit_iff_coprime m n).mpr hcop)
    rw [lpsUnaryQuadraticGauss_coprime_mul m n hcop a,mul_pow,
      ihm (a*(n:ℤ)) hum,ihn (a*(m:ℤ)) hun,lpsGaussFourthFactor_coprime_mul m n hcop]
    push_cast
    ring
end QEC.Coding.TannerLiftedProduct
