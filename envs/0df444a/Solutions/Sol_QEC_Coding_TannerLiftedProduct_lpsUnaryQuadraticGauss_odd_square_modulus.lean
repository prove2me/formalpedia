-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_odd_square_modulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:56:37.695563+00:00
-- url     : https://prove2.me/submissions/673e3c24-1457-4ed1-ac6f-b51135a4b86e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_odd_square_scale
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_inflate


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N d k : ℕ) [NeZero N]
    (hN : N=d^2*k) (hd : 0 < d) (hk : 0 < k) (a : ℤ)
    (ha : IsUnit (a:ZMod N)) (h2 : IsUnit (2:ZMod N)) :
    lpsUnaryQuadraticGauss a N=(d:ℂ)*lpsUnaryQuadraticGauss a k := by
  let : NeZero d := ⟨ne_of_gt hd⟩
  let : NeZero k := ⟨ne_of_gt hk⟩
  have hi := lpsUnaryQuadraticGauss_inflate (d^2) k a
  rw [← hN] at hi
  norm_num only [Nat.cast_pow] at hi
  rw [lpsUnaryQuadraticGauss_odd_square_scale N d k hN hd hk a ha h2] at hi
  have hdC : (d:ℂ)≠0 := by exact_mod_cast ne_of_gt hd
  apply mul_left_cancel₀ hdC
  calc
    _ = (d:ℂ)^2*lpsUnaryQuadraticGauss a k := hi
    _ = _ := by ring
end QEC.Coding.TannerLiftedProduct
