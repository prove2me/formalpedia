-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsZMod_unit_odd_of_even_modulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:48:58.32394+00:00
-- url     : https://prove2.me/submissions/d5845155-c283-4842-9de5-7b450041b7b0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsZMod_unit_descend

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 2 ∣ N)
    (a : ℤ) (ha : IsUnit (a:ZMod N)) : Odd a := by
  have hu := lpsZMod_unit_descend N 2 hN a ha
  apply Int.not_even_iff_odd.mp
  rintro ⟨k,hk⟩
  have hz : (a:ZMod 2)=0 := by
    rw [hk]
    push_cast
    rw [← two_mul,show (2:ZMod 2)=0 by decide,zero_mul]
  exact hu.ne_zero hz
end QEC.Coding.TannerLiftedProduct
