-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_two_pow_fourth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:57:09.847043+00:00
-- url     : https://prove2.me/submissions/b168961b-851a-45d2-bb0d-8265062166e8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_four_fourth
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_eight_fourth
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsZMod_unit_descend
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsZMod_unit_bezout
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsZMod_unit_odd_of_even_modulus
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_square_modulus


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (e : ℕ) (a : ℤ)
    (ha : IsUnit (a:ZMod (2^(e+2)))) :
    lpsUnaryQuadraticGauss a (2^(e+2))^4= -4*((2^(e+2):ℕ):ℂ)^2 := by
  induction e using Nat.twoStepInduction generalizing a with
  | zero =>
    have ho := lpsZMod_unit_odd_of_even_modulus 4 (by decide) a ha
    exact lpsUnaryQuadraticGauss_four_fourth a ho
  | one =>
    have ho := lpsZMod_unit_odd_of_even_modulus 8 (by decide) a ha
    exact lpsUnaryQuadraticGauss_eight_fourth a ho
  | more e ih0 ih1 =>
    have hN : 2^(e+2+2)=4*2^2*2^e := by rw [pow_add,pow_add];ring
    have hOld : 4*2^e=2^(e+2) := by rw [pow_add];ring
    obtain ⟨b,u,hdet⟩ := lpsZMod_unit_bezout (2^(e+2+2)) a ha
    rw [hN] at hdet
    have hs := lpsUnaryQuadraticGauss_square_modulus 2 (2^e) (by decide)
      (by positivity) a b u hdet
    rw [← hN,hOld] at hs
    have hd : 2^(e+2) ∣ 2^(e+2+2) := by
      conv_rhs => rw [pow_add]
      exact Nat.dvd_mul_right (2^(e+2)) (2^2)
    have hu := lpsZMod_unit_descend (2^(e+2+2)) (2^(e+2)) hd a ha
    rw [hs,mul_pow,ih0 a hu]
    norm_num only [Nat.cast_ofNat,Nat.cast_pow]
    rw [pow_add,pow_add]
    ring
end QEC.Coding.TannerLiftedProduct
