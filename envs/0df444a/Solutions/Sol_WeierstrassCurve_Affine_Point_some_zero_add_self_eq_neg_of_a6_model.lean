-- Prove2me | solution 1 for WeierstrassCurve.Affine.Point.some_zero_add_self_eq_neg_of_a6_model
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/8bc78b3a-8f54-5ff0-add9-07be06f2f223

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_Point_some_zero_add_self_eq_neg_of_a6_model

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

set_option autoImplicit false

theorem ws13_some_congr' {k : Type*} [Field k] {V : Affine k} {x₁ x₂ y₁ y₂ : k}
    {h₁ : V.Nonsingular x₁ y₁} {h₂ : V.Nonsingular x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : V.Point) = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

theorem solution
    {k : Type*} [Field k] [DecidableEq k] (B : k) (h2 : (2 : k) ≠ 0) {y : k} (hy0 : y ≠ 0)
    (h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular 0 y) :
    (WeierstrassCurve.Affine.Point.some 0 y h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Point)
      + WeierstrassCurve.Affine.Point.some 0 y h
      = -(WeierstrassCurve.Affine.Point.some 0 y h) := by
  have hyne : y ≠ Affine.negY (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k) 0 y := by
    simp only [Affine.negY]
    intro heq
    have : (2 : k) * y = 0 := by linear_combination heq
    rcases mul_eq_zero.mp this with h' | h'
    · exact h2 h'
    · exact hy0 h'
  rw [Point.add_of_Y_ne hyne, Point.neg_some]
  refine ws13_some_congr' ?_ ?_
  · rw [slope_of_Y_ne rfl hyne]
    simp only [Affine.addX, Affine.negY]
    ring
  · rw [slope_of_Y_ne rfl hyne]
    simp only [Affine.addY, Affine.negY, Affine.negAddY, Affine.addX]
    ring

end S_WeierstrassCurve_Affine_Point_some_zero_add_self_eq_neg_of_a6_model
end P2MW
export P2MW.S_WeierstrassCurve_Affine_Point_some_zero_add_self_eq_neg_of_a6_model (solution)
