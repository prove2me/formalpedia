-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticGauss_mask_sum_modulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:54:27.152507+00:00
-- url     : https://prove2.me/submissions/87467dc4-9ce9-497b-9619-3bbd259f7dfc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticGauss_mask_sum


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N d m : ℕ) [NeZero N] [NeZero d] [NeZero m]
    (hN : N=d*m) (a : ℤ) :
    (∑ j : Fin d, lpsQuadraticFourier N (a:ZMod N) (((m:ℤ)*j.val:ℤ):ZMod N)) =
      lpsUnaryQuadraticGauss (a*(d:ℤ)^2) N := by
  subst N
  exact lpsQuadraticGauss_mask_sum d m a
end QEC.Coding.TannerLiftedProduct
