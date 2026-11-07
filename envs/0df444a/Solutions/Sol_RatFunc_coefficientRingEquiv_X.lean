-- Prove2me | solution 1 for RatFunc.coefficientRingEquiv_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:05:01.37538+00:00
-- url     : https://prove2.me/submissions/2211af15-079f-4531-a83d-87e8c2d90eb4

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_RatFuncCoefficientEquiv
import Theorems.Thm_RatFunc_coefficientRingEquiv_apply_div
import Theorems.Thm_RatFunc_coefficientRingEquiv_C
attribute [local simp] RatFunc.coefficientRingEquiv_apply_div
attribute [local simp] RatFunc.coefficientRingEquiv_C

set_option autoImplicit false
open RatFunc
namespace RatFunc
theorem _root_.solution
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L) :
    coefficientRingEquiv e (RatFunc.X : RatFunc K) = RatFunc.X := by
  rw [show (RatFunc.X : RatFunc K) = algebraMap (Polynomial K) (RatFunc K)
      Polynomial.X / algebraMap (Polynomial K) (RatFunc K) 1 by simp,
    coefficientRingEquiv_apply_div]
  simp
end RatFunc
