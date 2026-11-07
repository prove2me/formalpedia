-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_four_fourth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:54:52.231856+00:00
-- url     : https://prove2.me/submissions/026375f3-7f55-4f7d-a009-1f36c9878918

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChar_four_odd_square
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_four

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : ℤ) (ha : Odd a) :
    lpsUnaryQuadraticGauss a 4^4= -4*(4:ℂ)^2 := by
  rw [lpsUnaryQuadraticGauss_four]
  have h := lpsChar_four_odd_square a ha
  linear_combination (16*ZMod.stdAddChar (a:ZMod 4)^2+64*ZMod.stdAddChar (a:ZMod 4)+80)*h
end QEC.Coding.TannerLiftedProduct
