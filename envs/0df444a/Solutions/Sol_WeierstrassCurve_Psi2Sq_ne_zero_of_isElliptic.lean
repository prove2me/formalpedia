-- Prove2me | solution 1 for WeierstrassCurve.Psi2Sq_ne_zero_of_isElliptic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/0e622a9b-5511-5797-9c37-1479ffd72b2d

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic.LinearCombination
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic

open Polynomial

theorem PortCard.sub_negY_sq_eq_eval_Ψ₂Sq {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    {x y : R} (e : W.toAffine.Equation x y) :
    (y - W.toAffine.negY x y) ^ 2 = W.Ψ₂Sq.eval x := by
  rw [WeierstrassCurve.Affine.equation_iff] at e
  simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  linear_combination 4 * e

theorem PortCard.two_smul_some_eq_zero_iff {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) :
    2 • WeierstrassCurve.Affine.Point.some x y h = 0 ↔ W.Ψ₂Sq.eval x = 0 := by
  have key : 2 • WeierstrassCurve.Affine.Point.some x y h = 0 ↔ y = W.toAffine.negY x y := by
    rw [two_nsmul, add_eq_zero_iff_eq_neg, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.some.injEq]
    simp
  rw [key, ← PortCard.sub_negY_sq_eq_eval_Ψ₂Sq W h.left, pow_eq_zero_iff two_ne_zero, sub_eq_zero]

theorem PortCard.Ψ₂Sq_ne_zero_of_isElliptic {F : Type*} [Field F] (W : WeierstrassCurve F)
    [W.IsElliptic] : W.Ψ₂Sq ≠ 0 := by
  intro h0
  rw [WeierstrassCurve.Ψ₂Sq_eq, Cubic.toPoly_eq_zero_iff] at h0
  have h4 : (4 : F) = 0 := congrArg Cubic.a h0
  have hb₂ : W.b₂ = 0 := congrArg Cubic.b h0
  have hb₆ : W.b₆ = 0 := congrArg Cubic.d h0
  have h2 : (2 : F) = 0 := by
    have h22 : (2 : F) * 2 = 0 := by linear_combination h4
    rcases mul_eq_zero.mp h22 with h | h <;> exact h
  have hΔ : W.Δ = 0 := by
    rw [show W.Δ = -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2 + 9 * W.b₂ * W.b₄ * W.b₆
      from rfl]
    linear_combination (-W.b₂ * W.b₈ + 9 * W.b₄ * W.b₆) * hb₂ + (-27 * W.b₆) * hb₆ +
      (-4 * W.b₄ ^ 3) * h2
  exact W.isUnit_Δ.ne_zero hΔ

theorem solution {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic] : W.Ψ₂Sq ≠ 0 :=
  PortCard.Ψ₂Sq_ne_zero_of_isElliptic W

end S_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic
end P2MW
export P2MW.S_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic (solution)
