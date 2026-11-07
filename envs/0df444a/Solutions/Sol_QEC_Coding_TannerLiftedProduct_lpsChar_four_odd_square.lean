-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChar_four_odd_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:53:42.712003+00:00
-- url     : https://prove2.me/submissions/1af40c90-b041-4bce-bdbe-0019f77f1b49

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChar_four_two

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : ℤ) (ha : Odd a) :
    ZMod.stdAddChar (a:ZMod 4)^2= -1 := by
  rw [pow_two,← AddChar.map_add_eq_mul]
  have he : (a:ZMod 4)+(a:ZMod 4)=2 := by
    obtain ⟨k,hk⟩ := ha
    rw [hk]
    push_cast
    have hz : (4:ZMod 4)=0 := by decide
    linear_combination (k:ZMod 4)*hz
  rw [he,lpsChar_four_two]
end QEC.Coding.TannerLiftedProduct
