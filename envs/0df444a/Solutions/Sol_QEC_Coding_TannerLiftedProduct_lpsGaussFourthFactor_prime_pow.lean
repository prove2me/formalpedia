-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGaussFourthFactor_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:58:54.162207+00:00
-- url     : https://prove2.me/submissions/3c573b2a-9240-4f31-946b-fd09fc366c0d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsZMod_unit_odd_of_even_modulus
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_odd_two
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_odd_prime_pow_fourth
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_two_pow_fourth
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p e : ℕ) (hp : p.Prime) (a : ℤ)
    (ha : IsUnit (a:ZMod (p^e))) :
    lpsUnaryQuadraticGauss a (p^e)^4=
      (lpsGaussFourthFactor (p^e):ℂ)*((p^e:ℕ):ℂ)^2 := by
  by_cases hp2 : p=2
  · subst p
    rcases e with _ | (_ | e)
    · simp [lpsGaussFourthFactor,lpsUnaryQuadraticGauss_one]
    · have ho := lpsZMod_unit_odd_of_even_modulus 2 (by decide) a ha
      simp [lpsGaussFourthFactor,lpsUnaryQuadraticGauss_odd_two a ho]
    · have hd4 : 4 ∣ 2^(e+2) := ⟨2^e,by rw [pow_add];ring⟩
      have hd2 : 2 ∣ 2^(e+2) := dvd_trans (show 2 ∣ 4 by decide) hd4
      simp only [lpsGaussFourthFactor,Nat.mod_eq_zero_of_dvd hd2,
        Nat.mod_eq_zero_of_dvd hd4,if_neg (by decide : ¬ (0:ℕ)=1),ite_true,
        Int.cast_neg,Int.cast_ofNat]
      exact lpsUnaryQuadraticGauss_two_pow_fourth e a ha
  · have ho : Odd (p^e) := (hp.odd_of_ne_two hp2).pow
    simp only [lpsGaussFourthFactor,Nat.odd_iff.mp ho,ite_true,Int.cast_one,one_mul]
    exact lpsUnaryQuadraticGauss_odd_prime_pow_fourth p hp hp2 e a ha
end QEC.Coding.TannerLiftedProduct
