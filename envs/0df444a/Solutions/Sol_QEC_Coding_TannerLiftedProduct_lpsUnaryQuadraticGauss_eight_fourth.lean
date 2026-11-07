-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_eight_fourth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:53:47.773163+00:00
-- url     : https://prove2.me/submissions/3056a500-667d-46c4-9112-5ae7f614ceca

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChar_eight_odd_fourth
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_eight

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : ℤ) (ha : Odd a) :
    lpsUnaryQuadraticGauss a 8^4= -4*(8:ℂ)^2 := by
  rw [lpsUnaryQuadraticGauss_eight a ha,mul_pow,lpsChar_eight_odd_fourth a ha]
  norm_num
end QEC.Coding.TannerLiftedProduct
