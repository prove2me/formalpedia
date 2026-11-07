-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChar_eight_odd_fourth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:52:32.146199+00:00
-- url     : https://prove2.me/submissions/18d3dda3-45c2-4893-ba28-c66cb86b485b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChar_eight_four

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : ℤ) (ha : Odd a) :
    ZMod.stdAddChar (a:ZMod 8)^4= -1 := by
  have he : (4:ZMod 8)*(a:ZMod 8)=4 := by
    obtain ⟨k,hk⟩ := ha
    rw [hk]
    push_cast
    have hz : (8:ZMod 8)=0 := by decide
    linear_combination (k:ZMod 8)*hz
  have h := AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N:=8)) 4 (a:ZMod 8)
  rw [nsmul_eq_mul] at h
  norm_num only [Nat.cast_ofNat] at h
  rw [he,lpsChar_eight_four] at h
  exact h.symm
end QEC.Coding.TannerLiftedProduct
