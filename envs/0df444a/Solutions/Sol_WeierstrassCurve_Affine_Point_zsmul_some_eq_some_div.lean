-- Prove2me | solution 1 for WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b36ea32d-f312-570b-bb72-33a56c8cce61

import Definitions.Def_WeierstrassCurve_EDSEngine
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FieldSimp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Logic.Embedding.Set
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Module.Torsion.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div

section PortCardMulX

namespace PortCard

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point Polynomial
open scoped Polynomial.Bivariate

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

theorem zsmul_some_eq_some_of_evalEval_ψ_ne_zero {x y : F} (h : W.toAffine.Nonsingular x y)
    {n : ℤ} (hψ : (W.ψ n).evalEval x y ≠ 0) :
    ∃ (x' y' : F) (h' : W.toAffine.Nonsingular x' y'),
      n • Point.some x y h = Point.some x' y' h' ∧
        x' * (W.ψ n).evalEval x y ^ 2 = (W.φ n).evalEval x y ∧
        x' * (W.ΨSq n).eval x = (W.Φ n).eval x := by
  have heq : W.toAffine.Equation x y := h.left
  have hψsq := W.evalEval_ψ_sq heq n
  have key := zsmul_eq_smulEval W h n
  have hVz : smulEval W x y n 2 ≠ 0 := hψ
  have hV := key ▸ (n • Jacobian.Point.fromAffine (Point.some x y h)).nonsingular
  have hQeq : (n • Jacobian.Point.fromAffine (Point.some x y h)) =
      Jacobian.Point.mk hV := Jacobian.Point.ext key
  refine ⟨smulEval W x y n 0 / smulEval W x y n 2 ^ 2,
    smulEval W x y n 1 / smulEval W x y n 2 ^ 3,
    (Jacobian.nonsingular_of_Z_ne_zero hVz).mp hV, ?_, ?_, ?_⟩
  · calc n • Point.some x y h
        = Jacobian.Point.toAffineAddEquiv W
            (n • Jacobian.Point.fromAffine (Point.some x y h)) := by
          rw [map_zsmul, ← Jacobian.Point.toAffineAddEquiv_symm_apply,
            AddEquiv.apply_symm_apply]
      _ = _ := by
          rw [hQeq, Jacobian.Point.toAffineAddEquiv_apply]
          exact Jacobian.Point.toAffineLift_of_Z_ne_zero hVz
  · show (W.φ n).evalEval x y / (W.ψ n).evalEval x y ^ 2 * (W.ψ n).evalEval x y ^ 2 =
        (W.φ n).evalEval x y
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 hψ)]
  · show (W.φ n).evalEval x y / (W.ψ n).evalEval x y ^ 2 * (W.ΨSq n).eval x = (W.Φ n).eval x
    rw [← hψsq, div_mul_cancel₀ _ (pow_ne_zero 2 hψ), W.evalEval_φ heq]

theorem zsmul_some_eq_some_of_eval_ΨSq_ne_zero {x y : F} (h : W.toAffine.Nonsingular x y)
    {n : ℤ} (hn : (W.ΨSq n).eval x ≠ 0) :
    ∃ (x' y' : F) (h' : W.toAffine.Nonsingular x' y'),
      n • Point.some x y h = Point.some x' y' h' ∧ x' * (W.ΨSq n).eval x = (W.Φ n).eval x := by
  have hψ : (W.ψ n).evalEval x y ≠ 0 := fun h0 =>
    hn (by rw [← W.evalEval_ψ_sq h.left n, h0]; exact zero_pow two_ne_zero)
  obtain ⟨x', y', h', hP, -, hx⟩ := zsmul_some_eq_some_of_evalEval_ψ_ne_zero W h hψ
  exact ⟨x', y', h', hP, hx⟩

theorem zsmul_some_eq_zero_iff_eval_ΨSq {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    n • Point.some x y h = 0 ↔ (W.ΨSq n).eval x = 0 := by
  rw [W.smul_eq_zero_iff_evalEval_ψ h n, ← W.evalEval_ψ_sq h.left n]
  exact ⟨fun h0 => by rw [h0]; exact zero_pow two_ne_zero, fun h0 => (sq_eq_zero_iff).mp h0⟩

theorem zsmul_some_eq_some_div {x y : F} (h : W.toAffine.Nonsingular x y) {n : ℤ}
    (hψ : (W.ψ n).evalEval x y ≠ 0) :
    ∃ (y' : F) (h' : W.toAffine.Nonsingular ((W.Φ n).eval x / (W.ΨSq n).eval x) y'),
      n • Point.some x y h = Point.some ((W.Φ n).eval x / (W.ΨSq n).eval x) y' h' := by
  obtain ⟨x', y', h', hP, -, hx⟩ := zsmul_some_eq_some_of_evalEval_ψ_ne_zero W h hψ
  have hΨ : (W.ΨSq n).eval x ≠ 0 := by
    rw [← W.evalEval_ψ_sq h.left n]; exact pow_ne_zero 2 hψ
  obtain rfl : x' = (W.Φ n).eval x / (W.ΨSq n).eval x := by rw [eq_div_iff hΨ]; exact hx
  exact ⟨y', h', hP⟩

end PortCard

end PortCardMulX

theorem solution {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) {n : ℤ} (hψ : (W.ψ n).evalEval x y ≠ 0) : ∃ (y' : F) (h' : W.toAffine.Nonsingular ((W.Φ n).eval x / (W.ΨSq n).eval x) y'), n • WeierstrassCurve.Affine.Point.some x y h = WeierstrassCurve.Affine.Point.some ((W.Φ n).eval x / (W.ΨSq n).eval x) y' h' :=
  PortCard.zsmul_some_eq_some_div W h hψ

end S_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
end P2MW
export P2MW.S_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div (solution)
