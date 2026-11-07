-- Prove2me | solution 1 for RatFunc.coefficientRingEquiv_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:30:36.08174+00:00
-- url     : https://prove2.me/submissions/7a02e097-444b-46a1-97c7-4e5f0d5b7ae6

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_RatFuncCoefficientEquiv
import Theorems.Thm_RatFunc_coefficientRingEquiv_apply_div
attribute [local simp] RatFunc.coefficientRingEquiv_apply_div

set_option autoImplicit false
open RatFunc
namespace RatFunc
theorem _root_.solution
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (a : K) :
    coefficientRingEquiv e (RatFunc.C a) = RatFunc.C (e a) := by
  rw [show RatFunc.C a = algebraMap (Polynomial K) (RatFunc K)
      (Polynomial.C a) / algebraMap (Polynomial K) (RatFunc K) 1 by simp,
    coefficientRingEquiv_apply_div]
  simp
end RatFunc
