-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_odd_prime_pow_fourth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:57:35.203495+00:00
-- url     : https://prove2.me/submissions/2d7d0d24-8767-4793-adbc-e1016feb005f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_prime_fourth
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_odd_square_modulus
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsZMod_unit_descend
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
theorem _root_.solution (p : ℕ) (hp : p.Prime) (hp2 : p≠2)
    (e : ℕ) (a : ℤ) (ha : IsUnit (a:ZMod (p^e))) :
    lpsUnaryQuadraticGauss a (p^e)^4=((p^e:ℕ):ℂ)^2 := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  induction e using Nat.twoStepInduction generalizing a with
  | zero => simp only [pow_zero,lpsUnaryQuadraticGauss_one,Nat.cast_one,one_pow]
  | one =>
    have ha' : IsUnit (a:ZMod p) :=
      Eq.mp (congrArg (fun N : ℕ => IsUnit (a:ZMod N)) (pow_one p)) ha
    simpa only [pow_one] using lpsUnaryQuadraticGauss_prime_fourth p hp2 a ha'.ne_zero
  | more e ih0 ih1 =>
    have hN : p^(e+2)=p^2*p^e := by rw [pow_add];ring
    have hodd : Odd (p^(e+2)) := (hp.odd_of_ne_two hp2).pow
    have h2 : IsUnit (2:ZMod (p^(e+2))) :=
      (ZMod.isUnit_iff_coprime 2 _).mpr hodd.coprime_two_left
    have hs := lpsUnaryQuadraticGauss_odd_square_modulus (p^(e+2)) p (p^e) hN
      hp.pos (pow_pos hp.pos e) a ha h2
    have hu := lpsZMod_unit_descend (p^(e+2)) (p^e)
      (by rw [hN];exact dvd_mul_left _ _) a ha
    rw [hs,mul_pow,ih0 a hu]
    norm_num only [Nat.cast_pow]
    rw [pow_add]
    ring
end QEC.Coding.TannerLiftedProduct
