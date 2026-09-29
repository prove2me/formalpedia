-- Prove2me | solution 1 for WeierstrassCurve.eval_Psi2Sq_of_two_nsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ce2fb3c1-c337-5a3c-b904-8ca7811a42a1

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_eval_Psi2Sq_of_two_nsmul_eq_zero

open WeierstrassCurve
open Polynomial

private lemma evalEval_ψ₂' {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y : R) :
    W.ψ₂.evalEval x y = 2 * y + W.a₁ * x + W.a₃ :=
  W.toAffine.evalEval_polynomialY x y

private lemma evalEval_ψ₂_sq_of_equation' {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    {x y : R} (h : W.toAffine.Equation x y) :
    W.ψ₂.evalEval x y ^ 2 = W.Ψ₂Sq.eval x := by
  have key := congrArg (Polynomial.evalEvalRingHom x y) W.ψ₂_sq
  simp only [map_add, map_mul, map_pow, map_ofNat, coe_evalEvalRingHom] at key
  rwa [show W.toAffine.polynomial.evalEval x y = 0 from h, mul_zero, add_zero, evalEval_C] at key

theorem solution {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve.Affine F} {x y : F} (h : W.Nonsingular x y)
    (h2 : 2 • (Affine.Point.some _ _ h : W.Point) = 0) : W.Ψ₂Sq.eval x = 0 := by
  have hψ : W.ψ₂.evalEval x y = 0 := by
    rw [two_nsmul, add_eq_zero_iff_eq_neg, Affine.Point.neg_some] at h2
    have hy := (Affine.Point.some.inj h2).right
    rw [evalEval_ψ₂']
    rw [Affine.negY] at hy
    linear_combination hy
  rw [← evalEval_ψ₂_sq_of_equation' W h.left, hψ, zero_pow two_ne_zero]

end S_WeierstrassCurve_eval_Psi2Sq_of_two_nsmul_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_eval_Psi2Sq_of_two_nsmul_eq_zero (solution)
