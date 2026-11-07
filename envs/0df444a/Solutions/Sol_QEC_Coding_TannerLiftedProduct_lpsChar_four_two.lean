-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChar_four_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:52:30.963612+00:00
-- url     : https://prove2.me/submissions/dff323f7-63c2-412b-8074-e18c933b7ee6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution : ZMod.stdAddChar (2:ZMod 4)= -1 := by
  have h := ZMod.stdAddChar_coe (N:=4) (2:ℤ)
  norm_num only [Int.cast_ofNat,Nat.cast_ofNat] at h
  rw [show (2:ℂ)*Real.pi*Complex.I*2/4=(Real.pi:ℂ)*Complex.I by ring] at h
  exact h.trans Complex.exp_pi_mul_I
end QEC.Coding.TannerLiftedProduct
