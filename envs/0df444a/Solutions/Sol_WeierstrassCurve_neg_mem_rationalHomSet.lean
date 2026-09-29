-- Prove2me | solution 1 for WeierstrassCurve.neg_mem_rationalHomSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/c7432a33-43dd-5d78-ae35-c76eb9fe0385

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_neg_mem_rationalHomSet

set_option autoImplicit false

open Polynomial
open scoped Polynomial.Bivariate

namespace RationalHomSetNeg

universe u v

variable {F : Type u} [Field F] (k : Type v) [Field k] [Algebra F k]

theorem evalEvalBC_eq (p : F[X][Y]) (x y : k) :
    WeierstrassCurve.evalEvalBC k p x y =
      ((evalEvalRingHom x y).comp (mapRingHom (mapRingHom (algebraMap F k)))) p := by
  rfl

theorem evalEvalBC_mul (p q : F[X][Y]) (x y : k) :
    WeierstrassCurve.evalEvalBC k (p * q) x y =
      WeierstrassCurve.evalEvalBC k p x y * WeierstrassCurve.evalEvalBC k q x y := by
  simp only [evalEvalBC_eq, map_mul]

theorem evalEvalBC_sub (p q : F[X][Y]) (x y : k) :
    WeierstrassCurve.evalEvalBC k (p - q) x y =
      WeierstrassCurve.evalEvalBC k p x y - WeierstrassCurve.evalEvalBC k q x y := by
  simp only [evalEvalBC_eq, map_sub]

theorem evalEvalBC_neg (p : F[X][Y]) (x y : k) :
    WeierstrassCurve.evalEvalBC k (-p) x y = -WeierstrassCurve.evalEvalBC k p x y := by
  simp only [evalEvalBC_eq, map_neg]

theorem evalEvalBC_C_C (c : F) (x y : k) :
    WeierstrassCurve.evalEvalBC k (C (C c)) x y = algebraMap F k c := by
  simp [WeierstrassCurve.evalEvalBC, Polynomial.evalEval]

theorem some_congr_y {W : WeierstrassCurve.Affine k} {x y₁ y₂ : k} (h₁ : W.Nonsingular x y₁)
    (hy : y₁ = y₂) :
    ∃ h₂ : W.Nonsingular x y₂, WeierstrassCurve.Affine.Point.some x y₁ h₁ = .some x y₂ h₂ := by
  subst hy; exact ⟨h₁, rfl⟩

variable [DecidableEq k]

theorem isRationallyRepresented_neg (W₁ W₂ : WeierstrassCurve F)
    (α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point)
    (hα : WeierstrassCurve.IsRationallyRepresented k W₁ W₂ α) :
    WeierstrassCurve.IsRationallyRepresented k W₁ W₂ (-α) := by
  obtain ⟨nX, dX, nY, dY, B, hB, hrep⟩ := hα
  refine ⟨nX, dX, -(nY * dX) - C (C W₂.a₁) * nX * dY - C (C W₂.a₃) * dX * dY, dY * dX, B, hB,
    fun x y h hx => ?_⟩
  obtain ⟨hdX, hdY, h', hαP⟩ := hrep x y h hx
  refine ⟨hdX, ?_, ?_⟩
  · rw [evalEvalBC_mul]; exact mul_ne_zero hdY hdX
  · have hneg : (-α) (.some x y h) = -(α (.some x y h)) := rfl
    rw [hneg, hαP, WeierstrassCurve.Affine.Point.neg_some]
    apply some_congr_y
    simp only [WeierstrassCurve.Affine.negY, evalEvalBC_sub, evalEvalBC_neg, evalEvalBC_mul,
      evalEvalBC_C_C]
    have ha₁ : (W₂.baseChange k).toAffine.a₁ = algebraMap F k W₂.a₁ := rfl
    have ha₃ : (W₂.baseChange k).toAffine.a₃ = algebraMap F k W₂.a₃ := rfl
    rw [ha₁, ha₃]
    field_simp

end RationalHomSetNeg

theorem solution
    {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [DecidableEq k]
    (W₁ W₂ : WeierstrassCurve F)
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) :
    -α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂ := by
  rcases hα with rfl | hα
  · rw [neg_zero]; exact WeierstrassCurve.zero_mem_rationalHomSet k W₁ W₂
  · exact Or.inr (RationalHomSetNeg.isRationallyRepresented_neg k W₁ W₂ α hα)

end S_WeierstrassCurve_neg_mem_rationalHomSet
end P2MW
export P2MW.S_WeierstrassCurve_neg_mem_rationalHomSet (solution)
