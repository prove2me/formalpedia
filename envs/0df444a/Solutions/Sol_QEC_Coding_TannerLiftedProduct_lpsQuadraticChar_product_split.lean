-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticChar_product_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:53:46.648235+00:00
-- url     : https://prove2.me/submissions/d0491633-d1c4-4b40-8fa8-2472bf375345

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChar_product_split

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m n : ℕ) [NeZero m] [NeZero n]
    (a x y : ℤ) :
    ZMod.stdAddChar (((a*((n:ℤ)*x+(m:ℤ)*y)^2):ℤ):ZMod (m*n)) =
      ZMod.stdAddChar (((a*(n:ℤ)*x^2):ℤ):ZMod m)*
      ZMod.stdAddChar (((a*(m:ℤ)*y^2):ℤ):ZMod n) := by
  have hz : ((m*n:ℕ):ZMod (m*n))=0 := ZMod.natCast_self _
  have he : (((a*((n:ℤ)*x+(m:ℤ)*y)^2):ℤ):ZMod (m*n)) =
      (((n:ℤ)*(a*(n:ℤ)*x^2)+(m:ℤ)*(a*(m:ℤ)*y^2):ℤ):ZMod (m*n)) := by
    push_cast at hz ⊢
    linear_combination (2:ZMod (m*n))*(a:ZMod (m*n))*(x:ZMod (m*n))*(y:ZMod (m*n))*hz
  rw [he,lpsChar_product_split]
end QEC.Coding.TannerLiftedProduct
