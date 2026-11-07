-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChar_product_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:52:29.795196+00:00
-- url     : https://prove2.me/submissions/40761711-27ae-4b52-9951-4f3a1a691ebb

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChar_inflate_modulus


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m n : ℕ) [NeZero m] [NeZero n] (x y : ℤ) :
    ZMod.stdAddChar (((n:ℤ)*x+(m:ℤ)*y:ℤ):ZMod (m*n)) =
      ZMod.stdAddChar (x:ZMod m)*ZMod.stdAddChar (y:ZMod n) := by
  rw [Int.cast_add,AddChar.map_add_eq_mul]
  rw [lpsChar_inflate_modulus (m*n) m n rfl,
    lpsChar_inflate_modulus (m*n) n m (Nat.mul_comm _ _)]
end QEC.Coding.TannerLiftedProduct
