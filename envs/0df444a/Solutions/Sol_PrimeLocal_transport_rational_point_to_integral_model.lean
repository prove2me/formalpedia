-- Prove2me | solution 1 for PrimeLocal.transport_rational_point_to_integral_model
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T00:49:47.444603+00:00
-- url     : https://prove2.me/submissions/1e9bf8e7-9309-44e2-80e9-caa9deae34cb

import Mathlib
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine NNReal
universe u v

namespace PrimeLocal
theorem _root_.solution (E : WeierstrassCurve ℚ) (W : WeierstrassCurve ℤ) (C : WeierstrassCurve.VariableChange ℚ) (hC : C • E = W.map (Int.castRingHom ℚ)) (hΔ : W.Δ ≠ 0) {p : ℕ} (P : (E⁄ℚ).Point) (hP : addOrderOf P = p) (hp : p.Prime) : ∃ (x y : ℚ) (h : (W.map (Int.castRingHom ℚ)).toAffine.Nonsingular x y) (h' : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular (algebraMap ℚ (AlgebraicClosure ℚ) x) (algebraMap ℚ (AlgebraicClosure ℚ) y)), addOrderOf (Point.some x y h) = p ∧ addOrderOf (Point.some _ _ h' : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = p ∧ ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • (Point.some _ _ h' : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = Point.some _ _ h'  := by
  classical
  change E.toAffine.Point at P
  let f : E.toAffine.Point →+ (C • E).toAffine.Point :=
    { toFun := Point.vcInvFun C E.toAffine
      map_zero' := rfl
      map_add' := Point.vcInvFun_add C E.toAffine }
  have hf : Function.Injective f := (Point.variableChangeEquiv C E.toAffine).symm.injective
  have hT : ∃ T : (W.map (Int.castRingHom ℚ)).toAffine.Point, addOrderOf T = p := by
    rw [← hC]
    exact ⟨f P, (addOrderOf_injective f hf P).trans hP⟩
  obtain ⟨T, hT⟩ := hT
  cases T with
  | zero =>
    have hz : addOrderOf (0 : (W.map (Int.castRingHom ℚ)).toAffine.Point) = 1 := addOrderOf_zero
    exact (hp.ne_one (hT.symm.trans hz)).elim
  | some x y h =>
    let b := Point.baseChange ℚ (AlgebraicClosure ℚ) (W' := (W.map (Int.castRingHom ℚ)).toAffine)
    have hb : Function.Injective b := Point.map_injective _
    have h' : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular
        (algebraMap ℚ (AlgebraicClosure ℚ) x) (algebraMap ℚ (AlgebraicClosure ℚ) y) :=
      ((W.map (Int.castRingHom ℚ)).toAffine.baseChange_nonsingular
        (f := Algebra.ofId ℚ (AlgebraicClosure ℚ)) (Algebra.ofId ℚ (AlgebraicClosure ℚ)).injective x y).mpr h
    refine ⟨x, y, h, h', hT, ?_, ?_⟩
    · exact (addOrderOf_injective b hb (Point.some x y h)).trans hT
    · intro σ
      change Point.map σ.toAlgHom (b (Point.some x y h)) = b (Point.some x y h)
      exact Point.map_baseChange σ.toAlgHom _
end PrimeLocal
