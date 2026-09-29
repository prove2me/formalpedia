-- Prove2me | solution 1 for WeierstrassCurve.two_mul_omega
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/734b0552-71f3-556d-a0e9-348ab5229b6e

import Definitions.Def_EllipticCurve_DivisionPolynomialOmega
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

namespace P2MW.S_WeierstrassCurve_two_mul_omega

section PortCardMulXY

namespace PortCard

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_two_mul_omega.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point Polynomial"
open scoped Polynomial.Bivariate

theorem zsmul_some_eq_some_jac {F : Type*} [Field F] [DecidableEq F] (V : WeierstrassCurve F)
    {x y : F} (h : V.toAffine.Nonsingular x y) {n : ℤ} (hψ : (V.ψ n).evalEval x y ≠ 0) :
    ∃ h' : V.toAffine.Nonsingular ((V.φ n).evalEval x y / (V.ψ n).evalEval x y ^ 2)
        ((V.ωe n).evalEval x y / (V.ψ n).evalEval x y ^ 3),
      n • Point.some x y h = Point.some ((V.φ n).evalEval x y / (V.ψ n).evalEval x y ^ 2)
        ((V.ωe n).evalEval x y / (V.ψ n).evalEval x y ^ 3) h' := by
  have key := zsmul_eq_smulEval V h n
  have hVz : smulEval V x y n 2 ≠ 0 := hψ
  have hV := key ▸ (n • Jacobian.Point.fromAffine (Point.some x y h)).nonsingular
  have hQeq : (n • Jacobian.Point.fromAffine (Point.some x y h)) =
      Jacobian.Point.mk hV := Jacobian.Point.ext key
  refine ⟨(Jacobian.nonsingular_of_Z_ne_zero hVz).mp hV, ?_⟩
  calc n • Point.some x y h
      = Jacobian.Point.toAffineAddEquiv V
          (n • Jacobian.Point.fromAffine (Point.some x y h)) := by
        rw [map_zsmul, ← Jacobian.Point.toAffineAddEquiv_symm_apply,
          AddEquiv.apply_symm_apply]
    _ = _ := by
        rw [hQeq, Jacobian.Point.toAffineAddEquiv_apply]
        exact Jacobian.Point.toAffineLift_of_Z_ne_zero hVz

theorem some_congr {F : Type*} [CommRing F] {V : Affine F} {x₁ x₂ y₁ y₂ : F} (ex : x₁ = x₂)
    (ey : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) :
    ∃ h₂ : V.Nonsingular x₂ y₂, Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst ex ey; exact ⟨h₁, rfl⟩

universe u v in

theorem exists_zsmul_some_eq_some_baseChange {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (n : ℤ) : ∃ ωe : R[X][Y], ∀ {F : Type v} [Field F] [DecidableEq F] [Algebra R F] {x y : F}
      (h : (W.baseChange F).toAffine.Nonsingular x y),
      ((W.baseChange F).ψ n).evalEval x y ≠ 0 →
        ∃ h' : (W.baseChange F).toAffine.Nonsingular
            (((W.baseChange F).Φ n).eval x / ((W.baseChange F).ΨSq n).eval x)
            ((ωe.map (mapRingHom (algebraMap R F))).evalEval x y /
              ((W.baseChange F).ψ n).evalEval x y ^ 3),
          n • Point.some x y h =
            Point.some (((W.baseChange F).Φ n).eval x / ((W.baseChange F).ΨSq n).eval x)
              ((ωe.map (mapRingHom (algebraMap R F))).evalEval x y /
                ((W.baseChange F).ψ n).evalEval x y ^ 3) h' := by
  refine ⟨W.ωe n, ?_⟩
  intro F _ _ _ x y h hψ
  have hω : (W.baseChange F).ωe n = (W.ωe n).map (mapRingHom (algebraMap R F)) := by
    rw [WeierstrassCurve.baseChange, map_ωe]
  obtain ⟨h₁, e₁⟩ := zsmul_some_eq_some_jac (W.baseChange F) h hψ
  have ex : ((W.baseChange F).φ n).evalEval x y / ((W.baseChange F).ψ n).evalEval x y ^ 2 =
      ((W.baseChange F).Φ n).eval x / ((W.baseChange F).ΨSq n).eval x := by
    rw [(W.baseChange F).evalEval_φ h.left n, (W.baseChange F).evalEval_ψ_sq h.left n]
  have ey : ((W.baseChange F).ωe n).evalEval x y / ((W.baseChange F).ψ n).evalEval x y ^ 3 =
      ((W.ωe n).map (mapRingHom (algebraMap R F))).evalEval x y /
        ((W.baseChange F).ψ n).evalEval x y ^ 3 := by
    rw [hω]
  obtain ⟨h₂, e₂⟩ := some_congr ex ey h₁
  exact ⟨h₂, e₁.trans e₂⟩

end PortCard

end PortCardMulXY

universe u v

section M4WilesOmega

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map Jacobian.nonsingular_of_Z_ne_zero Jacobian.Point.toAffineAddEquiv_symm_apply mk Jacobian Jacobian.Point.ext Jacobian.Point.fromAffine Jacobian.Point.toAffineAddEquiv_apply ΨSq toAffine Affine.Point Jacobian.Point.toAffineAddEquiv Jacobian.Point baseChange Jacobian.Point.toAffineLift_of_Z_ne_zero Jacobian.Point.mk ψDbl twoω Universal.curve Universal.map_specialize ω ω_eq_map_of_twoω_eq two_mul_ω_of_twoω_universal_eq map_specialize ψc ωe two_mul_ωe map_ωe smulEval zsmul_eq_smulEval evalEval_ψ_sq evalEval_φ"
p2m_open "WeierstrassCurve"

open Polynomial
open scoped Polynomial.Bivariate

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

lemma ψc_eq_ψDbl (n : ℤ) : W.ψc n = W.ψDbl n := rfl

lemma twoω_eq_two_mul_ωe (n : ℤ) : W.twoω n = 2 * W.ωe n := by
  rw [two_mul_ωe, ψc_eq_ψDbl, twoω]
  ring

namespace Universal p2m_export "WeierstrassCurve.Universal" "curve map_specialize" end Universal
p2m_open_scoped "WeierstrassCurve.Universal" in

lemma Universal.twoω_curve_eq (n : ℤ) : Universal.curve.twoω n = 2 * Universal.curve.ωe n :=
  twoω_eq_two_mul_ωe _ n

theorem ω_eq_ωe (n : ℤ) : W.ω n = W.ωe n := by
  rw [W.ω_eq_map_of_twoω_eq (Universal.twoω_curve_eq n), ← map_ωe, Universal.map_specialize]

private theorem _root_.WeierstrassCurve.two_mul_ω_eq_twoω (n : ℤ) : 2 * W.ω n = W.twoω n :=
  W.two_mul_ω_of_twoω_universal_eq (Universal.twoω_curve_eq n)

p2m_export "WeierstrassCurve" "two_mul_ω_eq_twoω"
end WeierstrassCurve

end M4WilesOmega

open Polynomial
open scoped Polynomial.Bivariate

theorem solution {R : Type*} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) : 2 * W.ω n = W.twoω n :=
  W.two_mul_ω_eq_twoω n

end S_WeierstrassCurve_two_mul_omega
end P2MW
export P2MW.S_WeierstrassCurve_two_mul_omega (solution)
