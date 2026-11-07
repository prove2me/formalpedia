-- Prove2me | solution 1 for RatFunc.num_coefficientRingEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:05:00.299374+00:00
-- url     : https://prove2.me/submissions/14203da4-ce47-42a2-9350-087cc5d19328

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_RatFuncCoefficientEquiv
import Theorems.Thm_RatFunc_coefficientRingEquiv_apply_div
import Theorems.Thm_RatFunc_denom_coefficientRingEquiv
attribute [local simp] RatFunc.coefficientRingEquiv_apply_div

set_option autoImplicit false
open RatFunc
namespace RatFunc
theorem _root_.solution
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    (x : RatFunc K) :
    (coefficientRingEquiv e x).num =
      x.num.map e.toRingHom := by
  let y := coefficientRingEquiv e x
  let P := x.num.map e.toRingHom
  let Q := x.denom.map e.toRingHom
  have hQ : Q ≠ 0 := Polynomial.map_ne_zero x.denom_ne_zero
  have hy : y = algebraMap (Polynomial L) (RatFunc L) P /
      algebraMap (Polynomial L) (RatFunc L) Q := by
    change coefficientRingEquiv e x = _
    rw [← x.num_div_denom]
    exact coefficientRingEquiv_apply_div e x.num x.denom
  have hcross : y.num * Q = P * y.denom :=
    (num_mul_eq_mul_denom_iff hQ).mpr hy
  rw [denom_coefficientRingEquiv e x] at hcross
  exact mul_right_cancel₀ hQ hcross
end RatFunc
