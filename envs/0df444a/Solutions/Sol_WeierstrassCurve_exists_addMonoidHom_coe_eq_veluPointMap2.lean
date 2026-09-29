-- Prove2me | solution 1 for WeierstrassCurve.exists_addMonoidHom_coe_eq_veluPointMap2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/fdcda89b-f43a-534b-881a-ab87c36585fb

import Mathlib
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Theorems.Thm_WeierstrassCurve_veluQuotient2_Delta_eq
import Theorems.Thm_WeierstrassCurve_velu2_secant_negAddY_cleared_identity
import Theorems.Thm_WeierstrassCurve_velu2_tangent_addX_cleared_identity
import Theorems.Thm_WeierstrassCurve_velu2_tangent_negAddY_cleared_identity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2

set_option Elab.async false

section PieceKernelExact

open Polynomial

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.slope_of_X_ne a₃ a₁ map Affine.nonsingular_iff mk a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.X_eq_iff Affine.negAddY Affine.Point.zero_def Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.nonsingular_neg Affine.equation_iff_nonsingular Affine.Point.some_ne_zero Δ c₄ Affine.addY Affine.Y_eq_of_X_eq Affine.Point.add_of_X_ne Affine.equation_iff Affine.Point.neg_some Affine.Point.add_self_of_Y_ne Δ' velu2X velu2Y veluPointMap2 veluPointMap2_zero veluPointMap2_some_of_eq veluPointMap2_some_of_ne veluQuotient2 veluQuotient2_a₁ veluQuotient2_a₂ veluQuotient2_a₃ veluQuotient2_a₄ veluGx veluGy veluGy_eq_zero_of_negY_eq veluQuotient2_Delta_eq velu2_secant_negAddY_cleared_identity velu2_tangent_addX_cleared_identity velu2_tangent_negAddY_cleared_identity"
p2m_open "WeierstrassCurve"

section NegYFixedPoint

variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {x₀ y₀ : R}

lemma negY_eq_of_veluGy_eq_zero (hgy : W.veluGy x₀ y₀ = 0) :
    W.toAffine.negY x₀ y₀ = y₀ := by
  simp only [veluGy] at hgy
  simp only [Affine.negY]
  linear_combination hgy

lemma veluGy_eq_zero_iff_negY_eq :
    W.veluGy x₀ y₀ = 0 ↔ W.toAffine.negY x₀ y₀ = y₀ :=
  ⟨negY_eq_of_veluGy_eq_zero, fun h => W.veluGy_eq_zero_of_negY_eq h⟩

end NegYFixedPoint

section FibreSingleton

variable {F : Type*} [Field F] {W : WeierstrassCurve F} {x₀ y₀ : F}

lemma eq_of_equation_of_veluGy_eq_zero (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) {y : F} (h : W.toAffine.Equation x₀ y) : y = y₀ := by
  rcases Affine.Y_eq_of_X_eq h hQ rfl with hy | hy
  · exact hy
  · rw [hy, negY_eq_of_veluGy_eq_zero hgy]

end FibreSingleton

end WeierstrassCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.slope_of_X_ne a₃ a₁ map Affine.nonsingular_iff mk a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.X_eq_iff Affine.negAddY Affine.Point.zero_def Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.nonsingular_neg Affine.equation_iff_nonsingular Affine.Point.some_ne_zero Δ c₄ Affine.addY Affine.Y_eq_of_X_eq Affine.Point.add_of_X_ne Affine.equation_iff Affine.Point.neg_some Affine.Point.add_self_of_Y_ne Δ' velu2X velu2Y veluPointMap2 veluPointMap2_zero veluPointMap2_some_of_eq veluPointMap2_some_of_ne veluQuotient2 veluQuotient2_a₁ veluQuotient2_a₂ veluQuotient2_a₃ veluQuotient2_a₄ veluGx veluGy veluGy_eq_zero_of_negY_eq veluQuotient2_Delta_eq velu2_secant_negAddY_cleared_identity velu2_tangent_addX_cleared_identity velu2_tangent_negAddY_cleared_identity"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY slope_of_X_ne Point.add_of_Y_eq slope nonsingular_iff map Point.some Point.some.injEq Point.X_eq_iff Nonsingular negAddY Point.zero_def nonsingular_add slope_of_Y_ne Point addX nonsingular_neg equation_iff_nonsingular Point.some_ne_zero addY Y_eq_of_X_eq Point.add_of_X_ne equation_iff polynomial Point.neg_some Point.add_self_of_Y_ne"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

section PointFibre

variable {F : Type*} [Field F] {W : Affine F} {x₀ y₀ : F}

namespace Point p2m_export "WeierstrassCurve.Affine.Point" "add_of_Y_eq some some.injEq X_eq_iff zero_def map some_ne_zero add_of_X_ne zero neg_some add_self_of_Y_ne mk" end Point
p2m_open_scoped "WeierstrassCurve.Affine.Point" in

theorem Point.some_eq_of_X_eq_of_veluGy_eq_zero (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hns : W.toAffine.Nonsingular x₀ y₀)
    {x y : F} (h : W.toAffine.Nonsingular x y) (hx : x = x₀) :
    Point.some x y h = Point.some x₀ y₀ hns := by
  have hy : y = y₀ := eq_of_equation_of_veluGy_eq_zero hQ hgy (hx ▸ h.left)
  subst hx
  subst hy
  rfl

end PointFibre

section TwoTorsionOrder

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} {x₀ y₀ : F}

theorem two_nsmul_some_eq_zero_of_veluGy_eq_zero (hgy : W.veluGy x₀ y₀ = 0)
    (hns : W.toAffine.Nonsingular x₀ y₀) :
    2 • (Point.some x₀ y₀ hns : W.toAffine.Point) = 0 := by
  rw [two_nsmul]
  exact Point.add_of_Y_eq rfl (negY_eq_of_veluGy_eq_zero hgy).symm

end TwoTorsionOrder

end WeierstrassCurve.Affine

end PieceKernelExact

section Piece_KwVeluOrderTwoNeg
set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.slope_of_X_ne a₃ a₁ map Affine.nonsingular_iff mk a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.X_eq_iff Affine.negAddY Affine.Point.zero_def Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.nonsingular_neg Affine.equation_iff_nonsingular Affine.Point.some_ne_zero Δ c₄ Affine.addY Affine.Y_eq_of_X_eq Affine.Point.add_of_X_ne Affine.equation_iff Affine.Point.neg_some Affine.Point.add_self_of_Y_ne Δ' velu2X velu2Y veluPointMap2 veluPointMap2_zero veluPointMap2_some_of_eq veluPointMap2_some_of_ne veluQuotient2 veluQuotient2_a₁ veluQuotient2_a₂ veluQuotient2_a₃ veluQuotient2_a₄ veluGx veluGy veluGy_eq_zero_of_negY_eq veluQuotient2_Delta_eq velu2_secant_negAddY_cleared_identity velu2_tangent_addX_cleared_identity velu2_tangent_negAddY_cleared_identity"
p2m_open "WeierstrassCurve"

theorem kw_veluOrderTwoNeg_axiomAnchor : True := by
  have _h := Classical.em True
  have _q : Quot.mk (α := ℕ) (· = ·) 0 = Quot.mk (· = ·) 0 := Quot.sound rfl
  trivial

section Field

variable {F : Type*} [Field F] {W : WeierstrassCurve F} {x₀ y₀ : F}

theorem kw_velu2Y_negY (hgy : W.veluGy x₀ y₀ = 0) (x y : F) :
    W.velu2Y x₀ y₀ x (W.toAffine.negY x y)
      = (W.veluQuotient2 x₀ y₀).toAffine.negY (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y) := by
  have _ := kw_veluOrderTwoNeg_axiomAnchor
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  by_cases hx : x = x₀
  ·
    subst hx
    simp only [velu2Y, velu2X, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, div_zero, sub_zero, add_zero, Affine.negY, veluQuotient2_a₁, veluQuotient2_a₃]
  ·
    have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
    simp only [velu2Y, velu2X, Affine.negY, veluQuotient2_a₁, veluQuotient2_a₃]
    field_simp
    linear_combination W.veluGx x₀ y₀ * hord

variable [DecidableEq F]
variable (hchar : (2 : F) ≠ 0) (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
  (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)

omit [DecidableEq F] in

lemma kw_v2neg_some_congr {W' : Affine F} {x y₁ y₂ : F}
    {h₁ : W'.Nonsingular x y₁} {h₂ : W'.Nonsingular x y₂} (hy : y₁ = y₂) :
    Affine.Point.some x y₁ h₁ = Affine.Point.some x y₂ h₂ := by
  have _ := kw_veluOrderTwoNeg_axiomAnchor
  subst hy; rfl

include hchar hQ hgy hΔ in

theorem kw_veluPointMap2_neg (P : W.toAffine.Point) :
    veluPointMap2 hchar hQ hgy hΔ (-P) = -veluPointMap2 hchar hQ hgy hΔ P := by
  have _ := kw_veluOrderTwoNeg_axiomAnchor
  cases P with
  | zero => rfl
  | some x y h =>
    rw [Affine.Point.neg_some]
    by_cases hx : x = x₀
    · rw [veluPointMap2_some_of_eq hchar hQ hgy hΔ _ hx,
        veluPointMap2_some_of_eq hchar hQ hgy hΔ h hx]
      rfl
    · rw [veluPointMap2_some_of_ne hchar hQ hgy hΔ _ hx,
        veluPointMap2_some_of_ne hchar hQ hgy hΔ h hx, Affine.Point.neg_some]
      exact kw_v2neg_some_congr (kw_velu2Y_negY hgy x y)

end Field

end WeierstrassCurve
end Piece_KwVeluOrderTwoNeg

section Piece_KwVeluOrderTwoAddKernel
set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.slope_of_X_ne a₃ a₁ map Affine.nonsingular_iff mk a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.X_eq_iff Affine.negAddY Affine.Point.zero_def Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.nonsingular_neg Affine.equation_iff_nonsingular Affine.Point.some_ne_zero Δ c₄ Affine.addY Affine.Y_eq_of_X_eq Affine.Point.add_of_X_ne Affine.equation_iff Affine.Point.neg_some Affine.Point.add_self_of_Y_ne Δ' velu2X velu2Y veluPointMap2 veluPointMap2_zero veluPointMap2_some_of_eq veluPointMap2_some_of_ne veluQuotient2 veluQuotient2_a₁ veluQuotient2_a₂ veluQuotient2_a₃ veluQuotient2_a₄ veluGx veluGy veluGy_eq_zero_of_negY_eq veluQuotient2_Delta_eq velu2_secant_negAddY_cleared_identity velu2_tangent_addX_cleared_identity velu2_tangent_negAddY_cleared_identity"
p2m_open "WeierstrassCurve"

theorem kw_veluOrderTwoAddKernel_axiomAnchor : True := by
  have _h := Classical.em True
  have _q : Quot.mk (α := ℕ) (· = ·) 0 = Quot.mk (· = ·) 0 := Quot.sound rfl
  trivial

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ : F}

omit [DecidableEq F] in

theorem kw_veluGx_ne_zero_of_quotΔ (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) :
    W.veluGx x₀ y₀ ≠ 0 := fun h =>
  hΔ (by rw [veluQuotient2_Delta_eq hQ hgy, h]; ring)

theorem kw_velu2_addX_kernel {x y : F} (hP : W.toAffine.Equation x y)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) (hx : x ≠ x₀) :
    W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀)
      = x₀ + W.veluGx x₀ y₀ / (x - x₀) := by
  have _ := kw_veluOrderTwoAddKernel_axiomAnchor
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  rw [Affine.equation_iff] at hP hQ
  simp only [Affine.slope_of_X_ne hx, Affine.addX, veluGx]
  field_simp
  linear_combination hP - hQ - (y - y₀) * hord

omit [DecidableEq F] in

theorem kw_velu2X_sub_velu2X {x₁ x₂ : F} (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀) :
    W.velu2X x₀ y₀ x₁ - W.velu2X x₀ y₀ x₂
      = (x₁ - x₂) * ((x₁ - x₀) * (x₂ - x₀) - W.veluGx x₀ y₀)
          / ((x₁ - x₀) * (x₂ - x₀)) := by
  have _ := kw_veluOrderTwoAddKernel_axiomAnchor
  have hd₁ : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hx₁
  have hd₂ : x₂ - x₀ ≠ 0 := sub_ne_zero.mpr hx₂
  simp only [velu2X]
  field_simp
  ring

omit [DecidableEq F] in

theorem kw_velu2X_eq_iff {x₁ x₂ : F} (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀) :
    W.velu2X x₀ y₀ x₁ = W.velu2X x₀ y₀ x₂
      ↔ x₁ = x₂ ∨ (x₁ - x₀) * (x₂ - x₀) = W.veluGx x₀ y₀ := by
  have _ := kw_veluOrderTwoAddKernel_axiomAnchor
  have hd₁ : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hx₁
  have hd₂ : x₂ - x₀ ≠ 0 := sub_ne_zero.mpr hx₂
  rw [← sub_eq_zero, kw_velu2X_sub_velu2X hx₁ hx₂, div_eq_zero_iff, mul_eq_zero,
    sub_eq_zero, sub_eq_zero]
  simp only [mul_ne_zero hd₁ hd₂, or_false]

theorem kw_velu2X_addKernel {x y : F} (hP : W.toAffine.Equation x y)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
    (ht : W.veluGx x₀ y₀ ≠ 0) (hx : x ≠ x₀) :
    W.velu2X x₀ y₀ (W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀))
      = W.velu2X x₀ y₀ x := by
  have _ := kw_veluOrderTwoAddKernel_axiomAnchor
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have htd : W.veluGx x₀ y₀ / (x - x₀) ≠ 0 := div_ne_zero ht hd
  rw [kw_velu2_addX_kernel hP hQ hgy hx]
  simp only [velu2X, add_sub_cancel_left]
  field_simp
  ring

theorem kw_velu2_addY_kernel {x y : F} (hP : W.toAffine.Equation x y)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) (hx : x ≠ x₀) :
    W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀) - y₀
      = -(W.veluGx x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀)) / (x - x₀) ^ 2 := by
  have _ := kw_veluOrderTwoAddKernel_axiomAnchor
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have hxP := kw_velu2_addX_kernel hP hQ hgy hx
  simp only [Affine.addY, Affine.negAddY, Affine.negY, Affine.slope_of_X_ne hx] at hxP ⊢
  rw [hxP]
  field_simp
  linear_combination -((x - x₀) ^ 2 * hord)

theorem kw_velu2Y_addKernel {x y : F} (hP : W.toAffine.Equation x y)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
    (ht : W.veluGx x₀ y₀ ≠ 0) (hx : x ≠ x₀) :
    W.velu2Y x₀ y₀ (W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀))
        (W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀))
      = W.velu2Y x₀ y₀ x y := by
  have _ := kw_veluOrderTwoAddKernel_axiomAnchor
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have hxP := kw_velu2_addX_kernel hP hQ hgy hx
  have hyP := kw_velu2_addY_kernel hP hQ hgy hx
  simp only [velu2Y]
  have htd : W.veluGx x₀ y₀ / (x - x₀) ≠ 0 := div_ne_zero ht hd

  rw [hxP, add_sub_cancel_left]

  have key : W.veluGx x₀ y₀
        * (W.a₁ * (W.veluGx x₀ y₀ / (x - x₀))
            + W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀) - y₀)
        / (W.veluGx x₀ y₀ / (x - x₀)) ^ 2
      = y₀ - y := by
    rw [sub_eq_iff_eq_add.mp hyP]
    field_simp
    ring
  rw [key]
  linear_combination hyP

variable (hchar : (2 : F) ≠ 0) (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
  (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)

omit [DecidableEq F] in

lemma kw_v2ker_some_congr {W' : Affine F} {u₁ u₂ v₁ v₂ : F}
    {h₁ : W'.Nonsingular u₁ v₁} {h₂ : W'.Nonsingular u₂ v₂} (hX : u₁ = u₂) (hY : v₁ = v₂) :
    Affine.Point.some u₁ v₁ h₁ = Affine.Point.some u₂ v₂ h₂ := by
  have _ := kw_veluOrderTwoAddKernel_axiomAnchor
  subst hX; subst hY; rfl

include hchar hQ hgy hΔ in

theorem kw_veluPointMap2_add_kernel_gen (hQns : W.toAffine.Nonsingular x₀ y₀)
    (P : W.toAffine.Point) :
    veluPointMap2 hchar hQ hgy hΔ (P + .some x₀ y₀ hQns)
      = veluPointMap2 hchar hQ hgy hΔ P := by
  have _ := kw_veluOrderTwoAddKernel_axiomAnchor
  have ht : W.veluGx x₀ y₀ ≠ 0 := kw_veluGx_ne_zero_of_quotΔ hQ hgy hΔ

  have h2P₀ : (2 : ℕ) • (Affine.Point.some x₀ y₀ hQns : W.toAffine.Point) = 0 :=
    Affine.two_nsmul_some_eq_zero_of_veluGy_eq_zero hgy hQns
  cases P with
  | zero =>
    rw [← Affine.Point.zero_def, zero_add, Affine.Point.zero_def, veluPointMap2_zero]
    exact veluPointMap2_some_of_eq hchar hQ hgy hΔ hQns rfl
  | some x y h =>
    by_cases hx : x = x₀
    ·
      have hPP₀ : Affine.Point.some x y h = Affine.Point.some x₀ y₀ hQns :=
        Affine.Point.some_eq_of_X_eq_of_veluGy_eq_zero hQ hgy hQns h hx
      rw [hPP₀, ← two_nsmul, h2P₀, veluPointMap2_some_of_eq hchar hQ hgy hΔ hQns rfl]
      rfl
    ·
      have hnsA : W.toAffine.Nonsingular
          (W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀))
          (W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀)) :=
        Affine.nonsingular_add h hQns fun hc => hx hc.1
      have hPP₀ : Affine.Point.some x y h + Affine.Point.some x₀ y₀ hQns
          = Affine.Point.some _ _ hnsA := Affine.Point.add_of_X_ne hx

      have hxA : W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀) ≠ x₀ := by
        rw [kw_velu2_addX_kernel h.1 hQ hgy hx]
        simpa using div_ne_zero ht (sub_ne_zero.mpr hx)
      rw [hPP₀, veluPointMap2_some_of_ne hchar hQ hgy hΔ hnsA hxA,
        veluPointMap2_some_of_ne hchar hQ hgy hΔ h hx]
      exact kw_v2ker_some_congr (kw_velu2X_addKernel h.1 hQ hgy ht hx)
        (kw_velu2Y_addKernel h.1 hQ hgy ht hx)

end Field

end WeierstrassCurve
end Piece_KwVeluOrderTwoAddKernel

section Piece_KwVeluOrderTwoSecantXContent
set_option autoImplicit false

p2m_open "Polynomial WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2.WeierstrassCurve.Affine"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.slope_of_X_ne a₃ a₁ map Affine.nonsingular_iff mk a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.X_eq_iff Affine.negAddY Affine.Point.zero_def Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.nonsingular_neg Affine.equation_iff_nonsingular Affine.Point.some_ne_zero Δ c₄ Affine.addY Affine.Y_eq_of_X_eq Affine.Point.add_of_X_ne Affine.equation_iff Affine.Point.neg_some Affine.Point.add_self_of_Y_ne Δ' velu2X velu2Y veluPointMap2 veluPointMap2_zero veluPointMap2_some_of_eq veluPointMap2_some_of_ne veluQuotient2 veluQuotient2_a₁ veluQuotient2_a₂ veluQuotient2_a₃ veluQuotient2_a₄ veluGx veluGy veluGy_eq_zero_of_negY_eq veluQuotient2_Delta_eq velu2_secant_negAddY_cleared_identity velu2_tangent_addX_cleared_identity velu2_tangent_negAddY_cleared_identity"
p2m_open "WeierstrassCurve"

theorem kw_veluOrderTwoSecantXContent_axiomAnchor : True := by
  have _h := Classical.em True
  have _q : Quot.mk (α := ℕ) (· = ·) 0 = Quot.mk (· = ·) 0 := Quot.sound rfl
  trivial

section CommRing

variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {x₀ y₀ x₁ y₁ x₂ y₂ : R}

theorem kw_velu2_secX_SI2 (hP₁ : W.toAffine.Equation x₁ y₁)
    (hP₂ : W.toAffine.Equation x₂ y₂) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) :
    (x₁ - x₀) * (x₂ - x₀) * (x₁ - x₂) * ((x₁ - x₀) * (x₂ - x₀) - W.veluGx x₀ y₀)
      = ((x₂ - x₀) * (W.a₁ * (x₁ - x₀) + y₁ - y₀)
            + (x₁ - x₀) * (W.a₁ * (x₂ - x₀) + y₂ - y₀) - W.a₁ * ((x₁ - x₀) * (x₂ - x₀)))
        * ((x₂ - x₀) * (y₁ - y₀) - (x₁ - x₀) * (y₂ - y₀)) := by
  have _ := kw_veluOrderTwoSecantXContent_axiomAnchor
  rw [Affine.equation_iff] at hP₁ hP₂ hQ
  simp only [veluGx]
  linear_combination (-(x₂ - x₀) ^ 2) * hP₁ + (x₁ - x₀) ^ 2 * hP₂
    + (-(x₁ - x₂) * ((x₁ - x₀) + (x₂ - x₀))) * hQ
    + ((x₂ - x₀) ^ 2 * y₁ - (x₁ - x₀) ^ 2 * y₂
        + (x₁ - x₂) * ((x₁ - x₀) + (x₂ - x₀)) * y₀) * hord

theorem kw_velu2_secX_SI3 (hP₁ : W.toAffine.Equation x₁ y₁)
    (hP₂ : W.toAffine.Equation x₂ y₂) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) :
    ((y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) - (W.a₂ + x₀ + x₁ + x₂) * (x₁ - x₂) ^ 2)
        * ((x₂ - x₀) * (W.a₁ * (x₁ - x₀) + y₁ - y₀)
            + (x₁ - x₀) * (W.a₁ * (x₂ - x₀) + y₂ - y₀) - W.a₁ * ((x₁ - x₀) * (x₂ - x₀)))
      = (x₁ - x₂) * ((x₁ - x₀) * (x₂ - x₀) - W.veluGx x₀ y₀)
        * ((x₂ - x₀) * (y₁ - y₀) - (x₁ - x₀) * (y₂ - y₀)) := by
  have _ := kw_veluOrderTwoSecantXContent_axiomAnchor
  rw [Affine.equation_iff] at hP₁ hP₂ hQ
  simp only [veluGx]
  linear_combination
    (-W.a₁*x₀*x₁ + W.a₁*x₀*x₂ + W.a₁*x₁*x₂ - W.a₁*x₂^2 - x₀*y₁ + x₀*y₂ - x₁*y₀ + x₁*y₂ + x₂*y₀
     + x₂*y₁ - 2*x₂*y₂) * hP₁
    + (W.a₁*x₀*x₁ - W.a₁*x₀*x₂ - W.a₁*x₁^2 + W.a₁*x₁*x₂ + x₀*y₁ - x₀*y₂ + x₁*y₀ - 2*x₁*y₁
     + x₁*y₂ - x₂*y₀ + x₂*y₁) * hP₂
    + ((x₁ - x₂) * (W.a₁ * (x₁ - x₂) + 2 * (y₁ - y₂))) * hQ
    + (-(W.a₁ * (x₁ - x₂) + (y₁ - y₂))
        * ((x₂ - x₀) * (y₁ - y₀) - (x₁ - x₀) * (y₂ - y₀))) * hord

end CommRing

end WeierstrassCurve
end Piece_KwVeluOrderTwoSecantXContent

section Piece_KwVeluOrderTwoTangentYContent
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

p2m_open "Polynomial WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2.WeierstrassCurve.Affine"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.slope_of_X_ne a₃ a₁ map Affine.nonsingular_iff mk a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.X_eq_iff Affine.negAddY Affine.Point.zero_def Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.nonsingular_neg Affine.equation_iff_nonsingular Affine.Point.some_ne_zero Δ c₄ Affine.addY Affine.Y_eq_of_X_eq Affine.Point.add_of_X_ne Affine.equation_iff Affine.Point.neg_some Affine.Point.add_self_of_Y_ne Δ' velu2X velu2Y veluPointMap2 veluPointMap2_zero veluPointMap2_some_of_eq veluPointMap2_some_of_ne veluQuotient2 veluQuotient2_a₁ veluQuotient2_a₂ veluQuotient2_a₃ veluQuotient2_a₄ veluGx veluGy veluGy_eq_zero_of_negY_eq veluQuotient2_Delta_eq velu2_secant_negAddY_cleared_identity velu2_tangent_addX_cleared_identity velu2_tangent_negAddY_cleared_identity"
p2m_open "WeierstrassCurve"

theorem kw_veluOrderTwoTangentYContent_axiomAnchor : True := by
  have _h := Classical.em True
  have _q : Quot.mk (α := ℕ) (· = ·) 0 = Quot.mk (· = ·) 0 := Quot.sound rfl
  trivial

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ x y : F}

end Field

section CommRing

variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {x₀ y₀ x y : R}

theorem kw_velu2_tanY_SI2c (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) :
    (2 * y + W.a₁ * x + W.a₃) ^ 3 * ((x - x₀) ^ 2 - W.veluGx x₀ y₀) * (y - y₀)
        + (W.a₁ ^ 2 * (x - x₀)
              + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀))
          * (x - x₀) ^ 2
          * ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2
              + W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (2 * y + W.a₁ * x + W.a₃)
              - (W.a₂ + 2 * x + x₀) * (2 * y + W.a₁ * x + W.a₃) ^ 2)
        - ((x - x₀) ^ 2 - W.veluGx x₀ y₀) * (x - x₀)
          * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (2 * y + W.a₁ * x + W.a₃) ^ 2
      = 0 := by
  have _ := kw_veluOrderTwoTangentYContent_axiomAnchor
  rw [Affine.equation_iff] at hP hQ
  simp only [veluGx]
  linear_combination
    (-W.a₁^4*x^3 + 3*W.a₁^4*x^2*x₀ - 3*W.a₁^4*x*x₀^2 + W.a₁^4*x₀^3 + 6*W.a₁^3*x^2*y₀ - 12*W.a₁^3*x*x₀*y₀ + 6*W.a₁^3*x₀^2*y₀ - 8*W.a₁^2*W.a₂*x^3 + 12*W.a₁^2*W.a₂*x^2*x₀ - 4*W.a₁^2*W.a₂*x₀^3 - 6*W.a₁^2*W.a₄*x^2 + 12*W.a₁^2*W.a₄*x*x₀ - 6*W.a₁^2*W.a₄*x₀^2 - 10*W.a₁^2*x^4 + 16*W.a₁^2*x^3*x₀ - 6*W.a₁^2*x^2*x₀^2 + 4*W.a₁^2*x*x₀^3 + 8*W.a₁^2*x*y*y₀ - 12*W.a₁^2*x*y₀^2 - 4*W.a₁^2*x₀^4 - 8*W.a₁^2*x₀*y*y₀ + 12*W.a₁^2*x₀*y₀^2 + 16*W.a₁*W.a₂*x^2*y₀ - 16*W.a₁*W.a₂*x*x₀*y + 16*W.a₁*W.a₂*x₀^2*y - 8*W.a₁*W.a₂*x₀^2*y₀ - 8*W.a₁*W.a₄*x*y + 16*W.a₁*W.a₄*x*y₀ + 8*W.a₁*W.a₄*x₀*y - 8*W.a₁*W.a₄*x₀*y₀ + 8*W.a₁*W.a₆*y₀ + 8*W.a₁*x^3*y + 16*W.a₁*x^3*y₀ - 24*W.a₁*x^2*x₀*y + 16*W.a₁*x₀^3*y - 8*W.a₁*x₀^3*y₀ + 8*W.a₁*y^2*y₀ - 16*W.a₁*y*y₀^2 + 16*W.a₁*y₀^3 - 16*W.a₂^2*x^3 + 16*W.a₂^2*x^2*x₀ - 16*W.a₂^2*x₀^3 - 16*W.a₂*W.a₄*x^2 + 16*W.a₂*W.a₄*x*x₀ - 24*W.a₂*W.a₄*x₀^2 - 16*W.a₂*W.a₆*x₀ - 48*W.a₂*x^4 + 48*W.a₂*x^3*x₀ + 8*W.a₂*x^2*x₀^2 - 16*W.a₂*x*x₀^3 - 32*W.a₂*x₀^4 - 16*W.a₂*x₀*y^2 + 32*W.a₂*x₀*y*y₀ - 32*W.a₂*x₀*y₀^2 - 4*W.a₄^2*x - 4*W.a₄^2*x₀ - 8*W.a₄*W.a₆ - 24*W.a₄*x^3 + 32*W.a₄*x^2*x₀ - 16*W.a₄*x*x₀^2 - 24*W.a₄*x₀^3 - 8*W.a₄*y^2 + 16*W.a₄*y*y₀ - 16*W.a₄*y₀^2 + 8*W.a₆*x^2 - 16*W.a₆*x*x₀ - 16*W.a₆*x₀^2 - 36*x^5 + 36*x^4*x₀ + 8*x^2*x₀^3 + 8*x^2*y^2 - 16*x^2*y*y₀ + 16*x^2*y₀^2 - 16*x*x₀^4 - 16*x*x₀*y^2 + 32*x*x₀*y*y₀ - 32*x*x₀*y₀^2 - 16*x₀^5 - 16*x₀^2*y^2 + 32*x₀^2*y*y₀ - 32*x₀^2*y₀^2) * hP
    + (W.a₁^4*x^3 - 3*W.a₁^4*x^2*x₀ + 3*W.a₁^4*x*x₀^2 - W.a₁^4*x₀^3 - 6*W.a₁^3*x^2*y₀ + 12*W.a₁^3*x*x₀*y₀ - 6*W.a₁^3*x₀^2*y₀ + 8*W.a₁^2*W.a₂*x^3 - 12*W.a₁^2*W.a₂*x^2*x₀ + 4*W.a₁^2*W.a₂*x₀^3 + 6*W.a₁^2*W.a₄*x^2 - 12*W.a₁^2*W.a₄*x*x₀ + 6*W.a₁^2*W.a₄*x₀^2 + 10*W.a₁^2*x^4 - 16*W.a₁^2*x^3*x₀ + 6*W.a₁^2*x^2*x₀^2 - 4*W.a₁^2*x*x₀^3 + 12*W.a₁^2*x*y₀^2 + 4*W.a₁^2*x₀^4 - 12*W.a₁^2*x₀*y₀^2 - 24*W.a₁*W.a₂*x^2*y₀ + 16*W.a₁*W.a₂*x₀^2*y₀ - 24*W.a₁*W.a₄*x*y₀ + 16*W.a₁*W.a₄*x₀*y₀ - 8*W.a₁*W.a₆*y₀ - 24*W.a₁*x^3*y₀ + 16*W.a₁*x₀^3*y₀ - 8*W.a₁*y₀^3 + 16*W.a₂^2*x^3 + 24*W.a₂*W.a₄*x^2 + 16*W.a₂*W.a₆*x₀ + 40*W.a₂*x^4 - 16*W.a₂*x^3*x₀ + 16*W.a₂*x^2*x₀^2 + 16*W.a₂*x₀*y₀^2 + 12*W.a₄^2*x - 4*W.a₄^2*x₀ + 8*W.a₄*W.a₆ + 24*W.a₄*x^3 - 8*W.a₄*x^2*x₀ + 16*W.a₄*x*x₀^2 + 8*W.a₄*y₀^2 - 8*W.a₆*x^2 + 16*W.a₆*x*x₀ + 16*W.a₆*x₀^2 + 28*x^5 - 20*x^4*x₀ + 16*x^3*x₀^2 - 8*x^2*y₀^2 + 16*x*x₀*y₀^2 + 16*x₀^2*y₀^2) * hQ
    + (-W.a₁^4*x^3*y₀ + 3*W.a₁^4*x^2*x₀*y₀ - 3*W.a₁^4*x*x₀^2*y₀ + W.a₁^4*x₀^3*y₀ + W.a₁^3*W.a₂*x^3*x₀ - 3*W.a₁^3*W.a₂*x^2*x₀^2 + 3*W.a₁^3*W.a₂*x*x₀^3 - W.a₁^3*W.a₂*x₀^4 + W.a₁^3*W.a₄*x^3 - 3*W.a₁^3*W.a₄*x^2*x₀ + 3*W.a₁^3*W.a₄*x*x₀^2 - W.a₁^3*W.a₄*x₀^3 - W.a₁^3*x^5 + 3*W.a₁^3*x^4*x₀ - 2*W.a₁^3*x^3*x₀^2 - 2*W.a₁^3*x^2*x₀^3 + 3*W.a₁^3*x^2*y*y₀ + 3*W.a₁^3*x^2*y₀^2 + 3*W.a₁^3*x*x₀^4 - 2*W.a₁^3*x*x₀*y*y₀ - 9*W.a₁^3*x*x₀*y₀^2 - W.a₁^3*x₀^5 + 5*W.a₁^3*x₀^2*y₀^2 - W.a₁^2*W.a₂*W.a₃*x^3 + 3*W.a₁^2*W.a₂*W.a₃*x^2*x₀ - 3*W.a₁^2*W.a₂*W.a₃*x*x₀^2 + W.a₁^2*W.a₂*W.a₃*x₀^3 - 10*W.a₁^2*W.a₂*x^3*y₀ - 6*W.a₁^2*W.a₂*x^2*x₀*y + 14*W.a₁^2*W.a₂*x^2*x₀*y₀ + 4*W.a₁^2*W.a₂*x*x₀^2*y + 6*W.a₁^2*W.a₂*x*x₀^2*y₀ - 8*W.a₁^2*W.a₂*x₀^3*y₀ - 2*W.a₁^2*W.a₃*x^4 + 5*W.a₁^2*W.a₃*x^3*x₀ - 3*W.a₁^2*W.a₃*x^2*x₀^2 - W.a₁^2*W.a₃*x*x₀^3 + 4*W.a₁^2*W.a₃*x*y*y₀ - 3*W.a₁^2*W.a₃*x*y₀^2 + W.a₁^2*W.a₃*x₀^4 - 2*W.a₁^2*W.a₃*x₀*y*y₀ + W.a₁^2*W.a₃*x₀*y₀^2 - 3*W.a₁^2*W.a₄*x^2*y - 9*W.a₁^2*W.a₄*x^2*y₀ + 2*W.a₁^2*W.a₄*x*x₀*y + 20*W.a₁^2*W.a₄*x*x₀*y₀ - 10*W.a₁^2*W.a₄*x₀^2*y₀ + 3*W.a₁^2*x^4*y - 11*W.a₁^2*x^4*y₀ - 8*W.a₁^2*x^3*x₀*y + 16*W.a₁^2*x^3*x₀*y₀ - 2*W.a₁^2*x^2*x₀^2*y - 4*W.a₁^2*x^2*x₀^2*y₀ + 4*W.a₁^2*x*x₀^3*y + 10*W.a₁^2*x*x₀^3*y₀ + 8*W.a₁^2*x*y^2*y₀ - 8*W.a₁^2*x*y*y₀^2 - 6*W.a₁^2*x*y₀^3 - 8*W.a₁^2*x₀^4*y₀ - 2*W.a₁^2*x₀*y^2*y₀ + 8*W.a₁^2*x₀*y₀^3 + 12*W.a₁*W.a₂^2*x^3*x₀ - 16*W.a₁*W.a₂^2*x^2*x₀^2 + 4*W.a₁*W.a₂^2*x₀^4 + 2*W.a₁*W.a₂*W.a₃*x^2*y₀ - 8*W.a₁*W.a₂*W.a₃*x*x₀*y + 4*W.a₁*W.a₂*W.a₃*x₀^2*y + 2*W.a₁*W.a₂*W.a₃*x₀^2*y₀ + 8*W.a₁*W.a₂*W.a₄*x^3 - 2*W.a₁*W.a₂*W.a₄*x^2*x₀ - 16*W.a₁*W.a₂*W.a₄*x*x₀^2 + 10*W.a₁*W.a₂*W.a₄*x₀^3 - 8*W.a₁*W.a₂*x^5 + 34*W.a₁*W.a₂*x^4*x₀ - 20*W.a₁*W.a₂*x^3*x₀^2 - 10*W.a₁*W.a₂*x^2*x₀^3 - 8*W.a₁*W.a₂*x^2*y*y₀ + 20*W.a₁*W.a₂*x^2*y₀^2 - 4*W.a₁*W.a₂*x*x₀^4 - 16*W.a₁*W.a₂*x*x₀*y^2 + 16*W.a₁*W.a₂*x*x₀*y*y₀ + 8*W.a₁*W.a₂*x₀^5 + 4*W.a₁*W.a₂*x₀^2*y^2 - 16*W.a₁*W.a₂*x₀^2*y₀^2 + W.a₁*W.a₃^2*y*y₀ - W.a₁*W.a₃^2*y₀^2 - 4*W.a₁*W.a₃*W.a₄*x*y + 2*W.a₁*W.a₃*W.a₄*x*y₀ + 2*W.a₁*W.a₃*W.a₄*x₀*y + 4*W.a₁*W.a₃*x^3*y + 2*W.a₁*W.a₃*x^3*y₀ - 10*W.a₁*W.a₃*x^2*x₀*y - 2*W.a₁*W.a₃*x^2*x₀*y₀ - 4*W.a₁*W.a₃*x*x₀^2*y + 4*W.a₁*W.a₃*x*x₀^2*y₀ + 4*W.a₁*W.a₃*x₀^3*y + 2*W.a₁*W.a₃*x₀^3*y₀ + 6*W.a₁*W.a₃*y^2*y₀ - 8*W.a₁*W.a₃*y*y₀^2 + 2*W.a₁*W.a₃*y₀^3 + 6*W.a₁*W.a₄^2*x^2 - 11*W.a₁*W.a₄^2*x*x₀ + 5*W.a₁*W.a₄^2*x₀^2 + 4*W.a₁*W.a₄*x^4 + 2*W.a₁*W.a₄*x^3*x₀ - 16*W.a₁*W.a₄*x*x₀^3 - 8*W.a₁*W.a₄*x*y^2 + 20*W.a₁*W.a₄*x*y₀^2 + 10*W.a₁*W.a₄*x₀^4 + 2*W.a₁*W.a₄*x₀*y^2 - 14*W.a₁*W.a₄*x₀*y₀^2 - 8*W.a₁*W.a₆*y*y₀ + 8*W.a₁*W.a₆*y₀^2 - 10*W.a₁*x^6 + 25*W.a₁*x^5*x₀ - 5*W.a₁*x^4*x₀^2 - 12*W.a₁*x^3*x₀^3 + 8*W.a₁*x^3*y^2 - 16*W.a₁*x^3*y*y₀ + 20*W.a₁*x^3*y₀^2 + 2*W.a₁*x^2*x₀^4 - 18*W.a₁*x^2*x₀*y^2 + 16*W.a₁*x^2*x₀*y*y₀ + 2*W.a₁*x^2*x₀*y₀^2 - 4*W.a₁*x*x₀^5 - 12*W.a₁*x*x₀^2*y^2 + 16*W.a₁*x*x₀^2*y*y₀ - 4*W.a₁*x*x₀^2*y₀^2 + 4*W.a₁*x₀^6 + 4*W.a₁*x₀^3*y^2 - 16*W.a₁*x₀^3*y₀^2 + 4*W.a₁*y^3*y₀ - 8*W.a₁*y^2*y₀^2 + 4*W.a₁*y₀^4 - 4*W.a₂^2*W.a₃*x^3 + 8*W.a₂^2*W.a₃*x^2*x₀ - 4*W.a₂^2*W.a₃*x₀^3 - 8*W.a₂^2*x^3*y₀ + 16*W.a₂^2*x^2*x₀*y - 16*W.a₂^2*x^2*x₀*y₀ + 8*W.a₂^2*x₀^3*y₀ - 2*W.a₂*W.a₃^2*x₀*y + 2*W.a₂*W.a₃^2*x₀*y₀ - 2*W.a₂*W.a₃*W.a₄*x^2 + 8*W.a₂*W.a₃*W.a₄*x*x₀ - 6*W.a₂*W.a₃*W.a₄*x₀^2 - 14*W.a₂*W.a₃*x^4 + 20*W.a₂*W.a₃*x^3*x₀ + 6*W.a₂*W.a₃*x^2*x₀^2 - 4*W.a₂*W.a₃*x*x₀^3 - 8*W.a₂*W.a₃*x₀^4 - 12*W.a₂*W.a₃*x₀*y^2 + 16*W.a₂*W.a₃*x₀*y*y₀ - 4*W.a₂*W.a₃*x₀*y₀^2 + 8*W.a₂*W.a₄*x^2*y - 20*W.a₂*W.a₄*x^2*y₀ + 16*W.a₂*W.a₄*x*x₀*y - 16*W.a₂*W.a₄*x*x₀*y₀ + 12*W.a₂*W.a₄*x₀^2*y₀ + 16*W.a₂*W.a₆*x₀*y - 16*W.a₂*W.a₆*x₀*y₀ - 8*W.a₂*x^4*y - 12*W.a₂*x^4*y₀ + 32*W.a₂*x^3*x₀*y - 24*W.a₂*x^3*x₀*y₀ + 16*W.a₂*x^2*x₀^2*y - 28*W.a₂*x^2*x₀^2*y₀ + 8*W.a₂*x*x₀^3*y₀ + 16*W.a₂*x₀^4*y₀ - 8*W.a₂*x₀*y^3 + 16*W.a₂*x₀*y^2*y₀ - 8*W.a₂*x₀*y₀^3 - W.a₃^2*W.a₄*y + W.a₃^2*W.a₄*y₀ + W.a₃^2*x^2*y - W.a₃^2*x^2*y₀ - 2*W.a₃^2*x*x₀*y + 2*W.a₃^2*x*x₀*y₀ - 2*W.a₃^2*x₀^2*y + 2*W.a₃^2*x₀^2*y₀ + W.a₃*W.a₄^2*x - W.a₃*W.a₄^2*x₀ - 6*W.a₃*W.a₄*x^3 + 12*W.a₃*W.a₄*x^2*x₀ - 6*W.a₃*W.a₄*x₀^3 - 6*W.a₃*W.a₄*y^2 + 8*W.a₃*W.a₄*y*y₀ - 2*W.a₃*W.a₄*y₀^2 - 11*W.a₃*x^5 + 13*W.a₃*x^4*x₀ + 4*W.a₃*x^3*x₀^2 + 2*W.a₃*x^2*x₀^3 + 6*W.a₃*x^2*y^2 - 8*W.a₃*x^2*y*y₀ + 2*W.a₃*x^2*y₀^2 - 4*W.a₃*x*x₀^4 - 12*W.a₃*x*x₀*y^2 + 16*W.a₃*x*x₀*y*y₀ - 4*W.a₃*x*x₀*y₀^2 - 4*W.a₃*x₀^5 - 12*W.a₃*x₀^2*y^2 + 16*W.a₃*x₀^2*y*y₀ - 4*W.a₃*x₀^2*y₀^2 + 8*W.a₄^2*x*y - 14*W.a₄^2*x*y₀ + 6*W.a₄^2*x₀*y₀ + 8*W.a₄*W.a₆*y - 8*W.a₄*W.a₆*y₀ - 12*W.a₄*x^3*y₀ + 16*W.a₄*x^2*x₀*y - 16*W.a₄*x^2*x₀*y₀ + 16*W.a₄*x*x₀^2*y - 16*W.a₄*x*x₀^2*y₀ + 12*W.a₄*x₀^3*y₀ - 4*W.a₄*y^3 + 8*W.a₄*y^2*y₀ - 4*W.a₄*y₀^3 - 8*W.a₆*x^2*y + 8*W.a₆*x^2*y₀ + 16*W.a₆*x*x₀*y - 16*W.a₆*x*x₀*y₀ + 16*W.a₆*x₀^2*y - 16*W.a₆*x₀^2*y₀ - 8*x^5*y - 6*x^5*y₀ + 16*x^4*x₀*y - 6*x^4*x₀*y₀ + 16*x^3*x₀^2*y - 24*x^3*x₀^2*y₀ - 4*x^2*x₀^3*y₀ + 4*x^2*y^3 - 8*x^2*y^2*y₀ + 4*x^2*y₀^3 + 8*x*x₀^4*y₀ - 8*x*x₀*y^3 + 16*x*x₀*y^2*y₀ - 8*x*x₀*y₀^3 + 8*x₀^5*y₀ - 8*x₀^2*y^3 + 16*x₀^2*y^2*y₀ - 8*x₀^2*y₀^3) * hord

end CommRing

end WeierstrassCurve
end Piece_KwVeluOrderTwoTangentYContent

section Piece_KwVeluOrderTwoSecantAtoms
set_option autoImplicit false

p2m_open "Polynomial WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2.WeierstrassCurve.Affine"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.slope_of_X_ne a₃ a₁ map Affine.nonsingular_iff mk a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.X_eq_iff Affine.negAddY Affine.Point.zero_def Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.nonsingular_neg Affine.equation_iff_nonsingular Affine.Point.some_ne_zero Δ c₄ Affine.addY Affine.Y_eq_of_X_eq Affine.Point.add_of_X_ne Affine.equation_iff Affine.Point.neg_some Affine.Point.add_self_of_Y_ne Δ' velu2X velu2Y veluPointMap2 veluPointMap2_zero veluPointMap2_some_of_eq veluPointMap2_some_of_ne veluQuotient2 veluQuotient2_a₁ veluQuotient2_a₂ veluQuotient2_a₃ veluQuotient2_a₄ veluGx veluGy veluGy_eq_zero_of_negY_eq veluQuotient2_Delta_eq velu2_secant_negAddY_cleared_identity velu2_tangent_addX_cleared_identity velu2_tangent_negAddY_cleared_identity"
p2m_open "WeierstrassCurve"

theorem kw_veluOrderTwoSecantAtoms_axiomAnchor : True := by
  have _h := Classical.em True
  have _q : Quot.mk (α := ℕ) (· = ·) 0 = Quot.mk (· = ·) 0 := Quot.sound rfl
  trivial

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ x₁ y₁ x₂ y₂ : F}

theorem kw_velu2_dXA_cleared (hx12 : x₁ ≠ x₂) :
    (x₁ - x₂) ^ 2 * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀)
      = (y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂)
          - (W.a₂ + x₀ + x₁ + x₂) * (x₁ - x₂) ^ 2 := by
  have _ := kw_veluOrderTwoSecantAtoms_axiomAnchor
  have hd₁₂ : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx12
  simp only [Affine.addX, Affine.slope_of_X_ne hx12]
  field_simp
  ring

variable (hx12 : x₁ ≠ x₂) (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀)
  (hX12 : W.velu2X x₀ y₀ x₁ ≠ W.velu2X x₀ y₀ x₂)

include hx12 hx₁ hx₂ hX12 in

theorem kw_velu2_slopeDiff_cleared :
    ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂)
          (W.velu2Y x₀ y₀ x₁ y₁) (W.velu2Y x₀ y₀ x₂ y₂)
        - W.toAffine.slope x₁ x₂ y₁ y₂)
      * ((x₁ - x₀) * (x₂ - x₀)) * ((x₁ - x₀) * (x₂ - x₀) - W.veluGx x₀ y₀)
      = W.veluGx x₀ y₀
        * ((x₂ - x₀) * (W.a₁ * (x₁ - x₀) + y₁ - y₀)
            + (x₁ - x₀) * (W.a₁ * (x₂ - x₀) + y₂ - y₀)
            - W.a₁ * ((x₁ - x₀) * (x₂ - x₀))) := by
  have _ := kw_veluOrderTwoSecantAtoms_axiomAnchor
  have hd₁ : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hx₁
  have hd₂ : x₂ - x₀ ≠ 0 := sub_ne_zero.mpr hx₂
  have hd₁₂ : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx12
  have hX12' : W.velu2X x₀ y₀ x₁ - W.velu2X x₀ y₀ x₂ ≠ 0 := sub_ne_zero.mpr hX12

  have hD₁₂ : (x₁ - x₀) * (x₂ - x₀) - W.veluGx x₀ y₀ ≠ 0 := fun h =>
    hX12' (by rw [kw_velu2X_sub_velu2X hx₁ hx₂, h, mul_zero, zero_div])
  rw [Affine.slope_of_X_ne hX12, Affine.slope_of_X_ne hx12,
    kw_velu2X_sub_velu2X hx₁ hx₂]
  simp only [velu2Y]
  field_simp
  ring

include hx12 hx₁ hx₂ hX12 in

theorem kw_velu2_slopeSum_cleared :
    ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂)
          (W.velu2Y x₀ y₀ x₁ y₁) (W.velu2Y x₀ y₀ x₂ y₂)
        + W.toAffine.slope x₁ x₂ y₁ y₂ + W.a₁)
      * ((x₁ - x₀) * (x₂ - x₀)) * (x₁ - x₂) * ((x₁ - x₀) * (x₂ - x₀) - W.veluGx x₀ y₀)
      = (x₁ - x₂) * ((x₁ - x₀) * (x₂ - x₀))
          * ((x₂ - x₀) * (W.a₁ * (x₁ - x₀) + y₁ - y₀)
              + (x₁ - x₀) * (W.a₁ * (x₂ - x₀) + y₂ - y₀)
              - W.a₁ * ((x₁ - x₀) * (x₂ - x₀)))
        + ((x₁ - x₀) * (x₂ - x₀) - W.veluGx x₀ y₀) * ((x₁ - x₀) + (x₂ - x₀))
          * ((x₂ - x₀) * (y₁ - y₀) - (x₁ - x₀) * (y₂ - y₀)) := by
  have _ := kw_veluOrderTwoSecantAtoms_axiomAnchor
  have hd₁ : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hx₁
  have hd₂ : x₂ - x₀ ≠ 0 := sub_ne_zero.mpr hx₂
  have hd₁₂ : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx12
  have hX12' : W.velu2X x₀ y₀ x₁ - W.velu2X x₀ y₀ x₂ ≠ 0 := sub_ne_zero.mpr hX12
  have hD₁₂ : (x₁ - x₀) * (x₂ - x₀) - W.veluGx x₀ y₀ ≠ 0 := fun h =>
    hX12' (by rw [kw_velu2X_sub_velu2X hx₁ hx₂, h, mul_zero, zero_div])
  rw [Affine.slope_of_X_ne hX12, Affine.slope_of_X_ne hx12,
    kw_velu2X_sub_velu2X hx₁ hx₂]
  simp only [velu2Y]
  field_simp
  ring

end Field

end WeierstrassCurve
end Piece_KwVeluOrderTwoSecantAtoms

section Piece_KwVeluOrderTwoSecantCarrier
set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.slope_of_X_ne a₃ a₁ map Affine.nonsingular_iff mk a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.X_eq_iff Affine.negAddY Affine.Point.zero_def Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.nonsingular_neg Affine.equation_iff_nonsingular Affine.Point.some_ne_zero Δ c₄ Affine.addY Affine.Y_eq_of_X_eq Affine.Point.add_of_X_ne Affine.equation_iff Affine.Point.neg_some Affine.Point.add_self_of_Y_ne Δ' velu2X velu2Y veluPointMap2 veluPointMap2_zero veluPointMap2_some_of_eq veluPointMap2_some_of_ne veluQuotient2 veluQuotient2_a₁ veluQuotient2_a₂ veluQuotient2_a₃ veluQuotient2_a₄ veluGx veluGy veluGy_eq_zero_of_negY_eq veluQuotient2_Delta_eq velu2_secant_negAddY_cleared_identity velu2_tangent_addX_cleared_identity velu2_tangent_negAddY_cleared_identity"
p2m_open "WeierstrassCurve"

theorem kw_veluOrderTwoSecantCarrier_axiomAnchor : True := by
  have _h := Classical.em True
  have _q : Quot.mk (α := ℕ) (· = ·) 0 = Quot.mk (· = ·) 0 := Quot.sound rfl
  trivial

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} (x₀ y₀ : F)

private abbrev _root_.WeierstrassCurve.KwVeluOrderTwoSecantCompatDiffAvoidAt : Prop :=
  ∀ ⦃x₁ y₁ x₂ y₂ : F⦄, W.toAffine.Equation x₁ y₁ → W.toAffine.Equation x₂ y₂ →
    x₁ ≠ x₂ → x₁ ≠ x₀ → x₂ ≠ x₀ →
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) ≠ x₀ →
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)) ≠ x₀ →
    W.velu2X x₀ y₀ x₁ ≠ W.velu2X x₀ y₀ x₂
    ∧ W.velu2X x₀ y₀ (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
        = (W.veluQuotient2 x₀ y₀).toAffine.addX (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂)
            ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂)
              (W.velu2Y x₀ y₀ x₁ y₁) (W.velu2Y x₀ y₀ x₂ y₂))
    ∧ W.velu2Y x₀ y₀ (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
          (W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂))
        = (W.veluQuotient2 x₀ y₀).toAffine.addY
            (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂) (W.velu2Y x₀ y₀ x₁ y₁)
            ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂)
              (W.velu2Y x₀ y₀ x₁ y₁) (W.velu2Y x₀ y₀ x₂ y₂))

p2m_export "WeierstrassCurve" "KwVeluOrderTwoSecantCompatDiffAvoidAt"

private abbrev _root_.WeierstrassCurve.KwVeluOrderTwoTangentCompatAt : Prop :=
  ∀ ⦃x y : F⦄, W.toAffine.Equation x y → y ≠ W.toAffine.negY x y → x ≠ x₀ →
    W.toAffine.addX x x (W.toAffine.slope x x y y) ≠ x₀ →
    W.velu2Y x₀ y₀ x y
      ≠ (W.veluQuotient2 x₀ y₀).toAffine.negY (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y)
    ∧ W.velu2X x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
        = (W.veluQuotient2 x₀ y₀).toAffine.addX (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
            ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
              (W.velu2Y x₀ y₀ x y) (W.velu2Y x₀ y₀ x y))
    ∧ W.velu2Y x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
          (W.toAffine.addY x x y (W.toAffine.slope x x y y))
        = (W.veluQuotient2 x₀ y₀).toAffine.addY
            (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y)
            ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
              (W.velu2Y x₀ y₀ x y) (W.velu2Y x₀ y₀ x y))

p2m_export "WeierstrassCurve" "KwVeluOrderTwoTangentCompatAt"

variable {x₀ y₀}
variable (hchar : (2 : F) ≠ 0) (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
  (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)

include hchar hQ hgy hΔ in

theorem kw_veluPointMap2_add_of_secant_diffAvoid
    (hsec : W.KwVeluOrderTwoSecantCompatDiffAvoidAt x₀ y₀)
    {x₁ y₁ x₂ y₂ : F} (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx12 : x₁ ≠ x₂) (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀)
    (hsp : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) ≠ x₀)
    (hsm : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)) ≠ x₀) :
    veluPointMap2 hchar hQ hgy hΔ
        ((Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) + Affine.Point.some x₂ y₂ h₂)
      = veluPointMap2 hchar hQ hgy hΔ (Affine.Point.some x₁ y₁ h₁)
        + veluPointMap2 hchar hQ hgy hΔ (Affine.Point.some x₂ y₂ h₂) := by
  have _ := kw_veluOrderTwoSecantCarrier_axiomAnchor
  obtain ⟨hX12, hXeq, hYeq⟩ := hsec h₁.1 h₂.1 hx12 hx₁ hx₂ hsp hsm
  rw [Affine.Point.add_of_X_ne hx12, veluPointMap2_some_of_ne hchar hQ hgy hΔ _ hsp,
    veluPointMap2_some_of_ne hchar hQ hgy hΔ h₁ hx₁,
    veluPointMap2_some_of_ne hchar hQ hgy hΔ h₂ hx₂]
  rw [Affine.Point.add_of_X_ne hX12]
  exact kw_v2ker_some_congr hXeq hYeq

include hchar hQ hgy hΔ in

theorem kw_veluPointMap2_add_self_of_tangent
    (htan : W.KwVeluOrderTwoTangentCompatAt x₀ y₀)
    {x y : F} (h : W.toAffine.Nonsingular x y) (hy : y ≠ W.toAffine.negY x y) (hx : x ≠ x₀)
    (hx2 : W.toAffine.addX x x (W.toAffine.slope x x y y) ≠ x₀) :
    veluPointMap2 hchar hQ hgy hΔ
        ((Affine.Point.some x y h : W.toAffine.Point) + Affine.Point.some x y h)
      = veluPointMap2 hchar hQ hgy hΔ (Affine.Point.some x y h)
        + veluPointMap2 hchar hQ hgy hΔ (Affine.Point.some x y h) := by
  have _ := kw_veluOrderTwoSecantCarrier_axiomAnchor
  obtain ⟨hY, hXeq, hYeq⟩ := htan h.1 hy hx hx2
  rw [Affine.Point.add_self_of_Y_ne hy, veluPointMap2_some_of_ne hchar hQ hgy hΔ _ hx2,
    veluPointMap2_some_of_ne hchar hQ hgy hΔ h hx]
  rw [Affine.Point.add_self_of_Y_ne hY]
  exact kw_v2ker_some_congr hXeq hYeq

end Field

end WeierstrassCurve
end Piece_KwVeluOrderTwoSecantCarrier

section Piece_KwVeluOrderTwoSecantConjunctOne
set_option autoImplicit false

p2m_open "Polynomial WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2.WeierstrassCurve.Affine"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.slope_of_X_ne a₃ a₁ map Affine.nonsingular_iff mk a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.X_eq_iff Affine.negAddY Affine.Point.zero_def Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.nonsingular_neg Affine.equation_iff_nonsingular Affine.Point.some_ne_zero Δ c₄ Affine.addY Affine.Y_eq_of_X_eq Affine.Point.add_of_X_ne Affine.equation_iff Affine.Point.neg_some Affine.Point.add_self_of_Y_ne Δ' velu2X velu2Y veluPointMap2 veluPointMap2_zero veluPointMap2_some_of_eq veluPointMap2_some_of_ne veluQuotient2 veluQuotient2_a₁ veluQuotient2_a₂ veluQuotient2_a₃ veluQuotient2_a₄ veluGx veluGy veluGy_eq_zero_of_negY_eq veluQuotient2_Delta_eq velu2_secant_negAddY_cleared_identity velu2_tangent_addX_cleared_identity velu2_tangent_negAddY_cleared_identity"
p2m_open "WeierstrassCurve"

theorem kw_veluOrderTwoSecantConjunctOne_axiomAnchor : True := by
  have _h := Classical.em True
  have _q : Quot.mk (α := ℕ) (· = ·) 0 = Quot.mk (· = ·) 0 := Quot.sound rfl
  trivial

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ : F}

omit [DecidableEq F] in

theorem kw_velu2_quotNegY_sub_factored (hgy : W.veluGy x₀ y₀ = 0)
    {x : F} (y : F) (hx : x ≠ x₀) :
    (x - x₀) ^ 2
        * (W.velu2Y x₀ y₀ x y
            - (W.veluQuotient2 x₀ y₀).toAffine.negY (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y))
      = (y - W.toAffine.negY x y) * ((x - x₀) ^ 2 - W.veluGx x₀ y₀) := by
  have _ := kw_veluOrderTwoSecantConjunctOne_axiomAnchor
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  simp only [velu2X, velu2Y, Affine.negY, veluQuotient2_a₁, veluQuotient2_a₃, veluGx]
  field_simp
  linear_combination (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀) * hord

variable (hgy : W.veluGy x₀ y₀ = 0) (hQns : W.toAffine.Nonsingular x₀ y₀)

include hgy hQns in

theorem kw_velu2X_ne_of_diffAvoid
    {x₁ y₁ x₂ y₂ : F} (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx12 : x₁ ≠ x₂) (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀)
    (hsp : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) ≠ x₀)
    (hsm : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)) ≠ x₀) :
    W.velu2X x₀ y₀ x₁ ≠ W.velu2X x₀ y₀ x₂ := by
  have _ := kw_veluOrderTwoSecantConjunctOne_axiomAnchor
  intro hXeq
  have hd₁ : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hx₁

  have hfib : (x₁ - x₀) * (x₂ - x₀) = W.veluGx x₀ y₀ :=
    ((kw_velu2X_eq_iff hx₁ hx₂).mp hXeq).resolve_left hx12

  have hx₂eq : x₂ = W.toAffine.addX x₁ x₀ (W.toAffine.slope x₁ x₀ y₁ y₀) := by
    rw [kw_velu2_addX_kernel h₁.1 hQns.1 hgy hx₁]
    field_simp
    linear_combination hfib

  have hnsA : W.toAffine.Nonsingular
      (W.toAffine.addX x₁ x₀ (W.toAffine.slope x₁ x₀ y₁ y₀))
      (W.toAffine.addY x₁ x₀ y₁ (W.toAffine.slope x₁ x₀ y₁ y₀)) :=
    Affine.nonsingular_add h₁ hQns fun hxy => hx₁ hxy.1
  have hP1P0 : (Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) + Affine.Point.some x₀ y₀ hQns
      = Affine.Point.some _ _ hnsA :=
    Affine.Point.add_of_X_ne hx₁

  have hnegP₀ : -(Affine.Point.some x₀ y₀ hQns : W.toAffine.Point) = .some x₀ y₀ hQns := by
    rw [Affine.Point.neg_some]
    exact kw_v2ker_some_congr rfl (negY_eq_of_veluGy_eq_zero hgy)

  rcases (Affine.Point.X_eq_iff (h₁ := h₂) (h₂ := hnsA)).mp hx₂eq with hPeq | hPeq
  ·
    refine hsm ?_
    have hdiff : (Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) - Affine.Point.some x₂ y₂ h₂
        = Affine.Point.some x₀ y₀ hQns := by
      rw [hPeq, ← hP1P0, sub_add_cancel_left, hnegP₀]
    rw [sub_eq_add_neg, Affine.Point.neg_some, Affine.Point.add_of_X_ne hx12,
      Affine.Point.some.injEq] at hdiff
    exact hdiff.1
  ·
    refine hsp ?_
    have hsum : (Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) + Affine.Point.some x₂ y₂ h₂
        = Affine.Point.some x₀ y₀ hQns := by
      rw [hPeq, ← hP1P0, ← sub_eq_add_neg, sub_add_cancel_left, hnegP₀]
    rw [Affine.Point.add_of_X_ne hx12, Affine.Point.some.injEq] at hsum
    exact hsum.1

include hgy hQns in

theorem kw_velu2Y_ne_quotNegY_of_tangent
    {x y : F} (h : W.toAffine.Nonsingular x y) (hy : y ≠ W.toAffine.negY x y) (hx : x ≠ x₀)
    (hx2 : W.toAffine.addX x x (W.toAffine.slope x x y y) ≠ x₀) :
    W.velu2Y x₀ y₀ x y
      ≠ (W.veluQuotient2 x₀ y₀).toAffine.negY (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y) := by
  have _ := kw_veluOrderTwoSecantConjunctOne_axiomAnchor
  intro hcon
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx

  have hfact : (y - W.toAffine.negY x y) * ((x - x₀) ^ 2 - W.veluGx x₀ y₀) = 0 := by
    have h0 := kw_velu2_quotNegY_sub_factored hgy y hx
    rw [sub_eq_zero.mpr hcon, mul_zero] at h0
    exact h0.symm

  have hd2t : (x - x₀) ^ 2 = W.veluGx x₀ y₀ :=
    sub_eq_zero.mp ((mul_eq_zero.mp hfact).resolve_left (sub_ne_zero.mpr hy))

  have hxPP₀ : W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀) = x := by
    rw [kw_velu2_addX_kernel h.1 hQns.1 hgy hx, ← hd2t]
    field_simp
    ring

  have hnsA : W.toAffine.Nonsingular
      (W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀))
      (W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀)) :=
    Affine.nonsingular_add h hQns fun hxy => hx hxy.1
  have hPP₀ : (Affine.Point.some x y h : W.toAffine.Point) + Affine.Point.some x₀ y₀ hQns
      = Affine.Point.some _ _ hnsA :=
    Affine.Point.add_of_X_ne hx

  have hnegP₀ : -(Affine.Point.some x₀ y₀ hQns : W.toAffine.Point) = .some x₀ y₀ hQns := by
    rw [Affine.Point.neg_some]
    exact kw_v2ker_some_congr rfl (negY_eq_of_veluGy_eq_zero hgy)

  rcases (Affine.Point.X_eq_iff (h₁ := hnsA) (h₂ := h)).mp hxPP₀ with hPeq | hPeq
  ·
    rw [← hPP₀, add_eq_left] at hPeq
    exact Affine.Point.some_ne_zero hQns hPeq
  ·
    refine hx2 ?_
    have h2P : (Affine.Point.some x y h : W.toAffine.Point) + Affine.Point.some x y h
        = Affine.Point.some x₀ y₀ hQns := by
      have heq := hPP₀.trans hPeq
      rw [← hnegP₀, eq_neg_iff_add_eq_zero, add_right_comm, heq, neg_add_cancel]
    rw [Affine.Point.add_self_of_Y_ne hy, Affine.Point.some.injEq] at h2P
    exact h2P.1

end Field

end WeierstrassCurve
end Piece_KwVeluOrderTwoSecantConjunctOne

section Piece_KwVeluOrderTwoSecantAlign
set_option autoImplicit false
set_option maxHeartbeats 160000000
set_option maxRecDepth 100000

p2m_open "Polynomial WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2.WeierstrassCurve.Affine"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.slope_of_X_ne a₃ a₁ map Affine.nonsingular_iff mk a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.X_eq_iff Affine.negAddY Affine.Point.zero_def Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.nonsingular_neg Affine.equation_iff_nonsingular Affine.Point.some_ne_zero Δ c₄ Affine.addY Affine.Y_eq_of_X_eq Affine.Point.add_of_X_ne Affine.equation_iff Affine.Point.neg_some Affine.Point.add_self_of_Y_ne Δ' velu2X velu2Y veluPointMap2 veluPointMap2_zero veluPointMap2_some_of_eq veluPointMap2_some_of_ne veluQuotient2 veluQuotient2_a₁ veluQuotient2_a₂ veluQuotient2_a₃ veluQuotient2_a₄ veluGx veluGy veluGy_eq_zero_of_negY_eq veluQuotient2_Delta_eq velu2_secant_negAddY_cleared_identity velu2_tangent_addX_cleared_identity velu2_tangent_negAddY_cleared_identity"
p2m_open "WeierstrassCurve"

theorem kw_veluOrderTwoSecantAlign_axiomAnchor : True := by
  have _h := Classical.em True
  have _q : Quot.mk (α := ℕ) (· = ·) 0 = Quot.mk (· = ·) 0 := Quot.sound rfl
  trivial

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}
  {x₀ y₀ x₁ y₁ x₂ y₂ : F}

theorem kw_velu2_secX_align (hP₁ : W.toAffine.Equation x₁ y₁)
    (hP₂ : W.toAffine.Equation x₂ y₂) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) (hx12 : x₁ ≠ x₂) (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀)
    (hsp : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) ≠ x₀)
    (hX12 : W.velu2X x₀ y₀ x₁ ≠ W.velu2X x₀ y₀ x₂) :
    W.velu2X x₀ y₀ (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
      = (W.veluQuotient2 x₀ y₀).toAffine.addX (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂)
          ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂)
            (W.velu2Y x₀ y₀ x₁ y₁) (W.velu2Y x₀ y₀ x₂ y₂)) := by
  have _ := kw_veluOrderTwoSecantAlign_axiomAnchor
  have hSI2 := kw_velu2_secX_SI2 hP₁ hP₂ hQ hord
  have hSI3 := kw_velu2_secX_SI3 hP₁ hP₂ hQ hord
  have hd₁ : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hx₁
  have hd₂ : x₂ - x₀ ≠ 0 := sub_ne_zero.mpr hx₂
  have hd₁₂ : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx12
  have hX12' : W.velu2X x₀ y₀ x₁ - W.velu2X x₀ y₀ x₂ ≠ 0 := sub_ne_zero.mpr hX12
  have hD₁₂ : (x₁ - x₀) * (x₂ - x₀) - W.veluGx x₀ y₀ ≠ 0 := fun h =>
    hX12' (by rw [kw_velu2X_sub_velu2X hx₁ hx₂, h, mul_zero, zero_div])
  have hdA : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀ ≠ 0 := sub_ne_zero.mpr hsp
  rw [Affine.slope_of_X_ne hX12, kw_velu2X_sub_velu2X hx₁ hx₂]

  conv_lhs => rw [velu2X, add_comm]
  rw [← eq_sub_iff_add_eq, div_eq_iff hdA, ← sub_eq_zero]

  simp only [velu2X, velu2Y, Affine.slope_of_X_ne hx12, Affine.addX, veluQuotient2_a₁,
    veluQuotient2_a₂]
  field_simp [hd₁, hd₂, hd₁₂, hD₁₂]
  linear_combination
    (W.veluGx x₀ y₀ * (x₁ - x₂) * ((x₁ - x₀) * (x₂ - x₀) - W.veluGx x₀ y₀) * ((x₁ - x₂) ^ 2 * ((x₁ - x₀) * (x₂ - x₀)) + ((y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) - (W.a₂ + x₀ + x₁ + x₂) * (x₁ - x₂) ^ 2) * ((x₁ - x₀) + (x₂ - x₀)))) * hSI2
    + (-(W.veluGx x₀ y₀ * (x₁ - x₂) ^ 2 * ((x₁ - x₀) * (x₂ - x₀)) * ((x₂ - x₀) * (W.a₁ * (x₁ - x₀) + y₁ - y₀) + (x₁ - x₀) * (W.a₁ * (x₂ - x₀) + y₂ - y₀) - W.a₁ * ((x₁ - x₀) * (x₂ - x₀))))) * hSI3

theorem kw_velu2_secY_negAddY_align (hP₁ : W.toAffine.Equation x₁ y₁)
    (hP₂ : W.toAffine.Equation x₂ y₂) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) (hx12 : x₁ ≠ x₂) (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀)
    (hsp : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) ≠ x₀)
    (hX12 : W.velu2X x₀ y₀ x₁ ≠ W.velu2X x₀ y₀ x₂) :
    W.velu2Y x₀ y₀ (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
        (W.toAffine.negAddY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂))
      = (W.veluQuotient2 x₀ y₀).toAffine.negAddY (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂)
          (W.velu2Y x₀ y₀ x₁ y₁)
          ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂)
            (W.velu2Y x₀ y₀ x₁ y₁) (W.velu2Y x₀ y₀ x₂ y₂)) := by
  have _ := kw_veluOrderTwoSecantAlign_axiomAnchor
  have hSIY := velu2_secant_negAddY_cleared_identity hP₁ hP₂ hQ hord hx12
  have hXalign := kw_velu2_secX_align hP₁ hP₂ hQ hord hx12 hx₁ hx₂ hsp hX12
  have hd₁ : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hx₁
  have hd₂ : x₂ - x₀ ≠ 0 := sub_ne_zero.mpr hx₂
  have hd₁₂ : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx12
  have hX12' : W.velu2X x₀ y₀ x₁ - W.velu2X x₀ y₀ x₂ ≠ 0 := sub_ne_zero.mpr hX12
  have hdA : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀ ≠ 0 := sub_ne_zero.mpr hsp

  have hColQ :
      (W.velu2X x₀ y₀ x₂ - W.velu2X x₀ y₀ x₁)
          * (W.velu2Y x₀ y₀ (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
                (W.toAffine.negAddY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂))
              - W.velu2Y x₀ y₀ x₁ y₁)
        = (W.velu2X x₀ y₀ (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
              - W.velu2X x₀ y₀ x₁)
          * (W.velu2Y x₀ y₀ x₂ y₂ - W.velu2Y x₀ y₀ x₁ y₁) := by

    set xA := W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) with hxA_def
    set nAY := W.toAffine.negAddY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) with hnAY_def

    have hxA_rel : (x₁ - x₂) ^ 2 * (xA - x₀)
        = (y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂)
            - (W.a₂ + x₀ + x₁ + x₂) * (x₁ - x₂) ^ 2 := by
      rw [hxA_def]; simp only [Affine.slope_of_X_ne hx12, Affine.addX]; field_simp; ring
    have hnAY_rel : (x₁ - x₂) * (nAY - y₁) = (y₁ - y₂) * (xA - x₁) := by
      rw [hnAY_def, hxA_def]
      simp only [Affine.slope_of_X_ne hx12, Affine.addX, Affine.negAddY]; field_simp; ring
    simp only [velu2X, velu2Y]
    field_simp [hd₁, hd₂, hdA]
    refine mul_left_cancel₀ (pow_ne_zero 2 hd₁₂) ?_
    linear_combination
      ((W.veluGx x₀ y₀) * (x₁ - x₀) * (x₁ - x₂) * ((x₁ - x₂)^2 * (W.a₂ + 2*x₁ + x₂) - (y₁ - y₂)^2 - W.a₁ * (y₁ - y₂) * (x₁ - x₂))) * hSIY
      + ((W.veluGx x₀ y₀) * (x₁ - x₀) * (x₂ - xA) * (W.a₁*x₀^3*x₁ - W.a₁*x₀^3*x₂ - W.a₁*x₀^2*x₁^2 - W.a₁*x₀^2*x₁*xA + W.a₁*x₀^2*x₂^2 + W.a₁*x₀^2*x₂*xA + W.a₁*x₀*x₁^2*x₂ + W.a₁*x₀*x₁^2*xA - W.a₁*x₀*x₁*x₂^2 - W.a₁*x₀*x₂^2*xA - W.a₁*x₁^2*x₂*xA + W.a₁*x₁*x₂^2*xA + (W.veluGx x₀ y₀)*x₀*y₁ - (W.veluGx x₀ y₀)*x₀*y₂ - (W.veluGx x₀ y₀)*x₁*y₀ + (W.veluGx x₀ y₀)*x₁*y₂ + (W.veluGx x₀ y₀)*x₂*y₀ - (W.veluGx x₀ y₀)*x₂*y₁ - x₀^3*y₁ + x₀^3*y₂ + 3*x₀^2*x₁*y₀ - 3*x₀^2*x₁*y₂ - 3*x₀^2*x₂*y₀ + 3*x₀^2*x₂*y₁ - 2*x₀*x₁^2*y₀ + 2*x₀*x₁^2*y₂ - x₀*x₁*x₂*y₁ + x₀*x₁*x₂*y₂ - 2*x₀*x₁*xA*y₀ + x₀*x₁*xA*y₁ + x₀*x₁*xA*y₂ + 2*x₀*x₂^2*y₀ - 2*x₀*x₂^2*y₁ + 2*x₀*x₂*xA*y₀ - x₀*x₂*xA*y₁ - x₀*x₂*xA*y₂ + x₁^2*x₂*y₀ - x₁^2*x₂*y₂ + x₁^2*xA*y₀ - x₁^2*xA*y₂ - x₁*x₂^2*y₀ + x₁*x₂^2*y₁ - x₁*x₂*xA*y₁ + x₁*x₂*xA*y₂ - x₂^2*xA*y₀ + x₂^2*xA*y₁)) * hxA_rel
      + ((x₁ - x₀) * (x₂ - x₀) * ((x₁ - x₀)*(x₂ - x₀) - (W.veluGx x₀ y₀)) * (W.a₁*(W.veluGx x₀ y₀)*x₁*y₁ - W.a₁*(W.veluGx x₀ y₀)*x₁*y₂ - W.a₁*(W.veluGx x₀ y₀)*x₂*y₁ + W.a₁*(W.veluGx x₀ y₀)*x₂*y₂ - W.a₂*(W.veluGx x₀ y₀)*x₁^2 + 2*W.a₂*(W.veluGx x₀ y₀)*x₁*x₂ - W.a₂*(W.veluGx x₀ y₀)*x₂^2 - (W.veluGx x₀ y₀)*x₀*x₁^2 + 2*(W.veluGx x₀ y₀)*x₀*x₁*x₂ - (W.veluGx x₀ y₀)*x₀*x₂^2 - (W.veluGx x₀ y₀)*x₁^3 + (W.veluGx x₀ y₀)*x₁^2*x₂ + (W.veluGx x₀ y₀)*x₁*x₂^2 - (W.veluGx x₀ y₀)*x₂^3 + (W.veluGx x₀ y₀)*y₁^2 - 2*(W.veluGx x₀ y₀)*y₁*y₂ + (W.veluGx x₀ y₀)*y₂^2 + x₀^3*x₁^2 - 2*x₀^3*x₁*x₂ + x₀^3*x₂^2 - x₀^2*x₁^3 + 2*x₀^2*x₁^2*x₂ - 2*x₀^2*x₁^2*xA - x₀^2*x₁*x₂^2 + 4*x₀^2*x₁*x₂*xA - 2*x₀^2*x₂^2*xA + 2*x₀*x₁^3*xA - 4*x₀*x₁^2*x₂*xA + x₀*x₁^2*xA^2 + 2*x₀*x₁*x₂^2*xA - 2*x₀*x₁*x₂*xA^2 + x₀*x₂^2*xA^2 - x₁^3*xA^2 + 2*x₁^2*x₂*xA^2 - x₁*x₂^2*xA^2)) * hnAY_rel

  conv_rhs => rw [Affine.negAddY, ← hXalign, Affine.slope_of_X_ne hX12]
  field_simp
  linear_combination -hColQ

theorem kw_velu2_secY_align (hP₁ : W.toAffine.Equation x₁ y₁)
    (hP₂ : W.toAffine.Equation x₂ y₂) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hx12 : x₁ ≠ x₂) (hx₁ : x₁ ≠ x₀) (hx₂ : x₂ ≠ x₀)
    (hsp : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) ≠ x₀)
    (hX12 : W.velu2X x₀ y₀ x₁ ≠ W.velu2X x₀ y₀ x₂) :
    W.velu2Y x₀ y₀ (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
        (W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂))
      = (W.veluQuotient2 x₀ y₀).toAffine.addY (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂)
          (W.velu2Y x₀ y₀ x₁ y₁)
          ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x₁) (W.velu2X x₀ y₀ x₂)
            (W.velu2Y x₀ y₀ x₁ y₁) (W.velu2Y x₀ y₀ x₂ y₂)) := by
  have _ := kw_veluOrderTwoSecantAlign_axiomAnchor
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  have hXalign := kw_velu2_secX_align hP₁ hP₂ hQ hord hx12 hx₁ hx₂ hsp hX12
  have hnAY := kw_velu2_secY_negAddY_align hP₁ hP₂ hQ hord hx12 hx₁ hx₂ hsp hX12
  rw [Affine.addY, kw_velu2Y_negY hgy, Affine.addY, hXalign, hnAY]

end Field

end WeierstrassCurve
end Piece_KwVeluOrderTwoSecantAlign

section Piece_KwVeluOrderTwoTangentXAlign
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8000

p2m_open "Polynomial WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2.WeierstrassCurve.Affine"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.slope_of_X_ne a₃ a₁ map Affine.nonsingular_iff mk a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.X_eq_iff Affine.negAddY Affine.Point.zero_def Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.nonsingular_neg Affine.equation_iff_nonsingular Affine.Point.some_ne_zero Δ c₄ Affine.addY Affine.Y_eq_of_X_eq Affine.Point.add_of_X_ne Affine.equation_iff Affine.Point.neg_some Affine.Point.add_self_of_Y_ne Δ' velu2X velu2Y veluPointMap2 veluPointMap2_zero veluPointMap2_some_of_eq veluPointMap2_some_of_ne veluQuotient2 veluQuotient2_a₁ veluQuotient2_a₂ veluQuotient2_a₃ veluQuotient2_a₄ veluGx veluGy veluGy_eq_zero_of_negY_eq veluQuotient2_Delta_eq velu2_secant_negAddY_cleared_identity velu2_tangent_addX_cleared_identity velu2_tangent_negAddY_cleared_identity"
p2m_open "WeierstrassCurve"

theorem kw_veluOrderTwoTangentXAlign_axiomAnchor : True := by
  have _h := Classical.em True
  have _q : Quot.mk (α := ℕ) (· = ·) 0 = Quot.mk (· = ·) 0 := Quot.sound rfl
  trivial

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ x y : F}

theorem kw_velu2_tan_d2P_cleared (hy : y ≠ W.toAffine.negY x y) :
    (W.toAffine.addX x x (W.toAffine.slope x x y y) - x₀) * (y - W.toAffine.negY x y) ^ 2
      = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2
        + W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (y - W.toAffine.negY x y)
        - (W.a₂ + 2 * x + x₀) * (y - W.toAffine.negY x y) ^ 2 := by
  have _ := kw_veluOrderTwoTangentXAlign_axiomAnchor
  have hsd : y - W.toAffine.negY x y ≠ 0 := sub_ne_zero.mpr hy
  simp only [Affine.slope_of_Y_ne rfl hy, Affine.addX]
  field_simp
  ring

theorem kw_velu2_tan_quotSlope_eq (hgy : W.veluGy x₀ y₀ = 0)
    (hx : x ≠ x₀) (hy : y ≠ W.toAffine.negY x y)
    (hY : W.velu2Y x₀ y₀ x y
      ≠ (W.veluQuotient2 x₀ y₀).toAffine.negY (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y)) :
    (W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
        (W.velu2Y x₀ y₀ x y) (W.velu2Y x₀ y₀ x y)
      = ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * ((x - x₀) ^ 2 - W.veluGx x₀ y₀)
            + W.veluGx x₀ y₀
              * (W.a₁ ^ 2 * (x - x₀)
                  + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀)))
          / ((y - W.toAffine.negY x y) * ((x - x₀) ^ 2 - W.veluGx x₀ y₀)) := by
  have _ := kw_veluOrderTwoTangentXAlign_axiomAnchor
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have hsd : y - W.toAffine.negY x y ≠ 0 := sub_ne_zero.mpr hy
  have hsdp : W.velu2Y x₀ y₀ x y
      - (W.veluQuotient2 x₀ y₀).toAffine.negY (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y) ≠ 0 :=
    sub_ne_zero.mpr hY

  have hD : (x - x₀) ^ 2 - W.veluGx x₀ y₀ ≠ 0 := by
    intro hD0
    refine hsdp ?_
    have h5a := kw_velu2_quotNegY_sub_factored hgy y hx
    rw [hD0, mul_zero] at h5a
    exact (mul_eq_zero.mp h5a).resolve_left (pow_ne_zero 2 hd)
  rw [Affine.slope_of_Y_ne rfl hY, div_eq_div_iff hsdp (mul_ne_zero hsd hD)]
  simp only [velu2X, velu2Y, veluQuotient2_a₁, veluQuotient2_a₂, veluQuotient2_a₃,
    veluQuotient2_a₄, Affine.negY, veluGx]
  field_simp
  linear_combination (-(3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀)
      * ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
            * ((x - x₀) ^ 2 - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀))
          + (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀)
            * (W.a₁ ^ 2 * (x - x₀)
                + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀)))) * hord

theorem kw_velu2_tanX_align (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hy : y ≠ W.toAffine.negY x y) (hx : x ≠ x₀)
    (hx2 : W.toAffine.addX x x (W.toAffine.slope x x y y) ≠ x₀)
    (hY : W.velu2Y x₀ y₀ x y
      ≠ (W.veluQuotient2 x₀ y₀).toAffine.negY (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y)) :
    W.velu2X x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
      = (W.veluQuotient2 x₀ y₀).toAffine.addX (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
          ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
            (W.velu2Y x₀ y₀ x y) (W.velu2Y x₀ y₀ x y)) := by
  have _ := kw_veluOrderTwoTangentXAlign_axiomAnchor
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have hsd : y - W.toAffine.negY x y ≠ 0 := sub_ne_zero.mpr hy
  have hD : (x - x₀) ^ 2 - W.veluGx x₀ y₀ ≠ 0 := by
    intro hD0
    refine sub_ne_zero.mpr hY ?_
    have h5a := kw_velu2_quotNegY_sub_factored hgy y hx
    rw [hD0, mul_zero] at h5a
    exact (mul_eq_zero.mp h5a).resolve_left (pow_ne_zero 2 hd)
  have hNpp := velu2_tangent_addX_cleared_identity hP hQ hord

  rw [kw_velu2_tan_quotSlope_eq hgy hx hy hY]
  conv_lhs => rw [velu2X, add_comm]
  rw [← eq_sub_iff_add_eq, div_eq_iff (sub_ne_zero.mpr hx2), ← sub_eq_zero]
  simp only [velu2X, Affine.slope_of_Y_ne rfl hy, Affine.addX, veluQuotient2_a₁,
    veluQuotient2_a₂]
  field_simp
  simp only [Affine.negY]
  linear_combination -W.veluGx x₀ y₀ * hNpp

end Field

end WeierstrassCurve
end Piece_KwVeluOrderTwoTangentXAlign

section Piece_KwVeluOrderTwoTangentYAlign
set_option autoImplicit false
set_option maxHeartbeats 160000000
set_option maxRecDepth 100000

p2m_open "Polynomial WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2.WeierstrassCurve.Affine"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.slope_of_X_ne a₃ a₁ map Affine.nonsingular_iff mk a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.X_eq_iff Affine.negAddY Affine.Point.zero_def Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.nonsingular_neg Affine.equation_iff_nonsingular Affine.Point.some_ne_zero Δ c₄ Affine.addY Affine.Y_eq_of_X_eq Affine.Point.add_of_X_ne Affine.equation_iff Affine.Point.neg_some Affine.Point.add_self_of_Y_ne Δ' velu2X velu2Y veluPointMap2 veluPointMap2_zero veluPointMap2_some_of_eq veluPointMap2_some_of_ne veluQuotient2 veluQuotient2_a₁ veluQuotient2_a₂ veluQuotient2_a₃ veluQuotient2_a₄ veluGx veluGy veluGy_eq_zero_of_negY_eq veluQuotient2_Delta_eq velu2_secant_negAddY_cleared_identity velu2_tangent_addX_cleared_identity velu2_tangent_negAddY_cleared_identity"
p2m_open "WeierstrassCurve"

theorem kw_veluOrderTwoTangentYAlign_axiomAnchor : True := by
  have _h := Classical.em True
  have _q : Quot.mk (α := ℕ) (· = ·) 0 = Quot.mk (· = ·) 0 := Quot.sound rfl
  trivial

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ x y : F}

theorem kw_velu2_tanY_negAddY_align (hP : W.toAffine.Equation x y)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
    (hy : y ≠ W.toAffine.negY x y) (hx : x ≠ x₀)
    (hx2 : W.toAffine.addX x x (W.toAffine.slope x x y y) ≠ x₀)
    (hY : W.velu2Y x₀ y₀ x y
      ≠ (W.veluQuotient2 x₀ y₀).toAffine.negY (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y)) :
    W.velu2Y x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
        (W.toAffine.negAddY x x y (W.toAffine.slope x x y y))
      = (W.veluQuotient2 x₀ y₀).toAffine.negAddY (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
          (W.velu2Y x₀ y₀ x y)
          ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
            (W.velu2Y x₀ y₀ x y) (W.velu2Y x₀ y₀ x y)) := by
  have _ := kw_veluOrderTwoTangentYAlign_axiomAnchor
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have hsd : y - W.toAffine.negY x y ≠ 0 := sub_ne_zero.mpr hy
  have hD : (x - x₀) ^ 2 - W.veluGx x₀ y₀ ≠ 0 := by
    intro hD0
    refine sub_ne_zero.mpr hY ?_
    have h5a := kw_velu2_quotNegY_sub_factored hgy y hx
    rw [hD0, mul_zero] at h5a
    exact (mul_eq_zero.mp h5a).resolve_left (pow_ne_zero 2 hd)
  have hd2P : W.toAffine.addX x x (W.toAffine.slope x x y y) - x₀ ≠ 0 := sub_ne_zero.mpr hx2
  have hsdEq : (2 * y + W.a₁ * x + W.a₃) = y - W.toAffine.negY x y := by
    simp only [Affine.negY]; ring
  have hSIYt := velu2_tangent_negAddY_cleared_identity hP hQ hord hy
  have hSI2c := kw_velu2_tanY_SI2c hP hQ hord

  rw [hsdEq] at hSI2c
  have hXalign := kw_velu2_tanX_align hP hQ hgy hy hx hx2 hY

  have hColQ :
      (W.velu2Y x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
              (W.toAffine.negAddY x x y (W.toAffine.slope x x y y))
            - W.velu2Y x₀ y₀ x y)
          * ((y - W.toAffine.negY x y) * ((x - x₀) ^ 2 - W.veluGx x₀ y₀))
        = ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * ((x - x₀) ^ 2 - W.veluGx x₀ y₀)
              + W.veluGx x₀ y₀
                * (W.a₁ ^ 2 * (x - x₀)
                    + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀)))
          * (W.velu2X x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
              - W.velu2X x₀ y₀ x) := by

    set x2P := W.toAffine.addX x x (W.toAffine.slope x x y y) with hx2P_def
    set nAY := W.toAffine.negAddY x x y (W.toAffine.slope x x y y) with hnAY_def

    have hx2P_rel : (x2P - x₀) * (y - W.toAffine.negY x y) ^ 2
        = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2
          + W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (y - W.toAffine.negY x y)
          - (W.a₂ + 2 * x + x₀) * (y - W.toAffine.negY x y) ^ 2 := by
      rw [hx2P_def]; exact kw_velu2_tan_d2P_cleared hy
    have hnAY_rel : (y - W.toAffine.negY x y) * (nAY - y)
        = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (x2P - x) := by
      rw [hnAY_def, hx2P_def]
      simp only [Affine.slope_of_Y_ne rfl hy, Affine.addX, Affine.negAddY]
      field_simp; ring
    simp only [velu2X, velu2Y]
    field_simp [hd, hd2P]
    refine mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 hsd) hd) ?_
    linear_combination
      (-W.veluGx x₀ y₀ * ((x - x₀) ^ 2 - W.veluGx x₀ y₀)
          * (y - W.toAffine.negY x y) ^ 3) * hSIYt
      + (-W.veluGx x₀ y₀ * (x2P - x) * ((x - x₀) * (x2P - x₀) - W.veluGx x₀ y₀)
          * (W.a₁ ^ 2 * (x - x₀)
              + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀))
          * (x - x₀) ^ 2) * hx2P_rel
      + ((x - x₀) * (y - W.toAffine.negY x y) ^ 2 * ((x - x₀) ^ 2 - W.veluGx x₀ y₀)
          * ((x - x₀) * (x2P - x₀) - W.veluGx x₀ y₀)
          * ((x - x₀) * (x2P - x₀) + W.veluGx x₀ y₀)) * hnAY_rel
      + (-W.veluGx x₀ y₀ * (x2P - x) * ((x - x₀) * (x2P - x₀) - W.veluGx x₀ y₀)) * hSI2c

  conv_rhs => rw [Affine.negAddY, ← hXalign, kw_velu2_tan_quotSlope_eq hgy hx hy hY]
  rw [div_mul_eq_mul_div, ← sub_eq_iff_eq_add, eq_div_iff (mul_ne_zero hsd hD)]
  linear_combination hColQ

theorem kw_velu2_tanY_align (hP : W.toAffine.Equation x y)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
    (hy : y ≠ W.toAffine.negY x y) (hx : x ≠ x₀)
    (hx2 : W.toAffine.addX x x (W.toAffine.slope x x y y) ≠ x₀)
    (hY : W.velu2Y x₀ y₀ x y
      ≠ (W.veluQuotient2 x₀ y₀).toAffine.negY (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y)) :
    W.velu2Y x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
        (W.toAffine.addY x x y (W.toAffine.slope x x y y))
      = (W.veluQuotient2 x₀ y₀).toAffine.addY (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
          (W.velu2Y x₀ y₀ x y)
          ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
            (W.velu2Y x₀ y₀ x y) (W.velu2Y x₀ y₀ x y)) := by
  have _ := kw_veluOrderTwoTangentYAlign_axiomAnchor
  have hXalign := kw_velu2_tanX_align hP hQ hgy hy hx hx2 hY
  have hnAY := kw_velu2_tanY_negAddY_align hP hQ hgy hy hx hx2 hY
  rw [Affine.addY, kw_velu2Y_negY hgy, Affine.addY, hXalign, hnAY]

end Field

end WeierstrassCurve
end Piece_KwVeluOrderTwoTangentYAlign

section PieceAbbrev

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.slope_of_X_ne a₃ a₁ map Affine.nonsingular_iff mk a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.X_eq_iff Affine.negAddY Affine.Point.zero_def Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.nonsingular_neg Affine.equation_iff_nonsingular Affine.Point.some_ne_zero Δ c₄ Affine.addY Affine.Y_eq_of_X_eq Affine.Point.add_of_X_ne Affine.equation_iff Affine.Point.neg_some Affine.Point.add_self_of_Y_ne Δ' velu2X velu2Y veluPointMap2 veluPointMap2_zero veluPointMap2_some_of_eq veluPointMap2_some_of_ne veluQuotient2 veluQuotient2_a₁ veluQuotient2_a₂ veluQuotient2_a₃ veluQuotient2_a₄ veluGx veluGy veluGy_eq_zero_of_negY_eq veluQuotient2_Delta_eq velu2_secant_negAddY_cleared_identity velu2_tangent_addX_cleared_identity velu2_tangent_negAddY_cleared_identity"
p2m_open "WeierstrassCurve"

section Held

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ : F}

variable (W x₀ y₀) in

private abbrev _root_.WeierstrassCurve.KwVeluOrderTwoAddCompatAt (h2 : (2 : F) ≠ 0) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) : Prop :=
  ∀ P Q : W.toAffine.Point,
    veluPointMap2 h2 hQ hgy hΔ (P + Q) = veluPointMap2 h2 hQ hgy hΔ P + veluPointMap2 h2 hQ hgy hΔ Q

p2m_export "WeierstrassCurve" "KwVeluOrderTwoAddCompatAt"
end Held

end WeierstrassCurve

end PieceAbbrev

section Piece_KwVeluOrderTwoAddCompatReduce
set_option autoImplicit false

p2m_open "Polynomial WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2.WeierstrassCurve.Affine"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.slope_of_X_ne a₃ a₁ map Affine.nonsingular_iff mk a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.X_eq_iff Affine.negAddY Affine.Point.zero_def Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.nonsingular_neg Affine.equation_iff_nonsingular Affine.Point.some_ne_zero Δ c₄ Affine.addY Affine.Y_eq_of_X_eq Affine.Point.add_of_X_ne Affine.equation_iff Affine.Point.neg_some Affine.Point.add_self_of_Y_ne Δ' velu2X velu2Y veluPointMap2 veluPointMap2_zero veluPointMap2_some_of_eq veluPointMap2_some_of_ne veluQuotient2 veluQuotient2_a₁ veluQuotient2_a₂ veluQuotient2_a₃ veluQuotient2_a₄ veluGx veluGy veluGy_eq_zero_of_negY_eq veluQuotient2_Delta_eq velu2_secant_negAddY_cleared_identity velu2_tangent_addX_cleared_identity velu2_tangent_negAddY_cleared_identity"
p2m_open "WeierstrassCurve"

theorem kw_veluOrderTwoAddCompatReduce_axiomAnchor : True := by
  have _h := Classical.em True
  have _q : Quot.mk (α := ℕ) (· = ·) 0 = Quot.mk (· = ·) 0 := Quot.sound rfl
  trivial

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ : F}

omit [DecidableEq F] in

theorem kw_velu2_kernel_nonsingular (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) :
    W.toAffine.Nonsingular x₀ y₀ := by
  have _ := kw_veluOrderTwoAddCompatReduce_axiomAnchor
  have ht : W.veluGx x₀ y₀ ≠ 0 := kw_veluGx_ne_zero_of_quotΔ hQ hgy hΔ
  simp only [veluGx] at ht
  refine (Affine.nonsingular_iff ..).mpr ⟨hQ, Or.inl fun hcon => ht ?_⟩
  linear_combination -hcon

variable (hchar : (2 : F) ≠ 0) (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
  (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)

include hchar hQ hgy hΔ in

theorem kw_veluPointMap2_add_of_right_ker {K : W.toAffine.Point}
    (hK : veluPointMap2 hchar hQ hgy hΔ K = 0) (P : W.toAffine.Point) :
    veluPointMap2 hchar hQ hgy hΔ (P + K) = veluPointMap2 hchar hQ hgy hΔ P := by
  have _ := kw_veluOrderTwoAddCompatReduce_axiomAnchor
  have hQns : W.toAffine.Nonsingular x₀ y₀ := kw_velu2_kernel_nonsingular hQ hgy hΔ
  cases K with
  | zero => rw [← Affine.Point.zero_def, add_zero]
  | some x y h =>
    by_cases hx : x = x₀
    ·
      rw [Affine.Point.some_eq_of_X_eq_of_veluGy_eq_zero hQ hgy hQns h hx]
      exact kw_veluPointMap2_add_kernel_gen hchar hQ hgy hΔ hQns P
    ·
      rw [veluPointMap2_some_of_ne hchar hQ hgy hΔ h hx] at hK
      exact absurd hK (Affine.Point.some_ne_zero _)

include hchar hQ hgy hΔ in

theorem kw_veluPointMap2_add_self (htan : W.KwVeluOrderTwoTangentCompatAt x₀ y₀)
    (P : W.toAffine.Point) :
    veluPointMap2 hchar hQ hgy hΔ (P + P)
      = veluPointMap2 hchar hQ hgy hΔ P + veluPointMap2 hchar hQ hgy hΔ P := by
  have _ := kw_veluOrderTwoAddCompatReduce_axiomAnchor
  have hQns : W.toAffine.Nonsingular x₀ y₀ := kw_velu2_kernel_nonsingular hQ hgy hΔ
  cases P with
  | zero =>
    rw [← Affine.Point.zero_def, add_zero, Affine.Point.zero_def, veluPointMap2_zero,
      ← Affine.Point.zero_def, add_zero]
  | some x y h =>
    by_cases hy : y = W.toAffine.negY x y
    ·
      have hPnP : (Affine.Point.some x y h : W.toAffine.Point) = -Affine.Point.some x y h := by
        rw [Affine.Point.neg_some]; exact kw_v2ker_some_congr rfl hy
      have h2P0 : (Affine.Point.some x y h : W.toAffine.Point) + .some x y h = 0 := by
        nth_rw 1 [hPnP]; exact neg_add_cancel _
      have h2φP : veluPointMap2 hchar hQ hgy hΔ (.some x y h)
          + veluPointMap2 hchar hQ hgy hΔ (.some x y h) = 0 := by
        nth_rw 1 [hPnP, kw_veluPointMap2_neg hchar hQ hgy hΔ]; exact neg_add_cancel _
      rw [h2P0, Affine.Point.zero_def, veluPointMap2_zero]
      exact h2φP.symm
    ·
      have hx : x ≠ x₀ := by
        intro hcon
        have hPP₀ : (Affine.Point.some x y h : W.toAffine.Point)
            = Affine.Point.some x₀ y₀ hQns :=
          Affine.Point.some_eq_of_X_eq_of_veluGy_eq_zero hQ hgy hQns h hcon
        rw [Affine.Point.some.injEq] at hPP₀
        exact hy (hcon ▸ hPP₀.2 ▸ (negY_eq_of_veluGy_eq_zero hgy).symm)
      by_cases hx2 : W.toAffine.addX x x (W.toAffine.slope x x y y) = x₀
      ·
        have hnsA : W.toAffine.Nonsingular
            (W.toAffine.addX x x (W.toAffine.slope x x y y))
            (W.toAffine.addY x x y (W.toAffine.slope x x y y)) :=
          Affine.nonsingular_add h h fun hxy => hy hxy.2
        have h2P : (Affine.Point.some x y h : W.toAffine.Point) + Affine.Point.some x y h
            = Affine.Point.some x₀ y₀ hQns := by
          rw [Affine.Point.add_self_of_Y_ne hy]
          exact Affine.Point.some_eq_of_X_eq_of_veluGy_eq_zero hQ hgy hQns hnsA hx2

        have hφ2P : veluPointMap2 hchar hQ hgy hΔ
            ((Affine.Point.some x y h : W.toAffine.Point) + Affine.Point.some x y h) = 0 := by
          rw [h2P]; exact veluPointMap2_some_of_eq hchar hQ hgy hΔ hQns rfl

        have hnegP₀ : -(Affine.Point.some x₀ y₀ hQns : W.toAffine.Point) = .some x₀ y₀ hQns := by
          rw [Affine.Point.neg_some]
          exact kw_v2ker_some_congr rfl (negY_eq_of_veluGy_eq_zero hgy)
        have hnegP : -(Affine.Point.some x y h : W.toAffine.Point)
            = Affine.Point.some x y h + Affine.Point.some x₀ y₀ hQns := by
          rw [← hnegP₀, ← sub_eq_add_neg, ← h2P]; abel
        have h2φP : veluPointMap2 hchar hQ hgy hΔ (.some x y h)
            + veluPointMap2 hchar hQ hgy hΔ (.some x y h) = 0 :=
          add_eq_zero_iff_eq_neg.mpr <| by
            rw [← kw_veluPointMap2_neg hchar hQ hgy hΔ, hnegP,
              kw_veluPointMap2_add_kernel_gen hchar hQ hgy hΔ hQns]
        rw [hφ2P, h2φP]
      ·
        exact kw_veluPointMap2_add_self_of_tangent hchar hQ hgy hΔ htan h hy hx hx2

include hchar hQ hgy hΔ in

theorem kw_veluPointMap2_add' (hsec : W.KwVeluOrderTwoSecantCompatDiffAvoidAt x₀ y₀)
    (htan : W.KwVeluOrderTwoTangentCompatAt x₀ y₀) (P₁ P₂ : W.toAffine.Point) :
    veluPointMap2 hchar hQ hgy hΔ (P₁ + P₂)
      = veluPointMap2 hchar hQ hgy hΔ P₁ + veluPointMap2 hchar hQ hgy hΔ P₂ := by
  have _ := kw_veluOrderTwoAddCompatReduce_axiomAnchor
  have hQns : W.toAffine.Nonsingular x₀ y₀ := kw_velu2_kernel_nonsingular hQ hgy hΔ
  cases P₁ with
  | zero =>
    rw [← Affine.Point.zero_def, zero_add, Affine.Point.zero_def, veluPointMap2_zero,
      ← Affine.Point.zero_def, zero_add]
  | some x₁ y₁ h₁ =>
    cases P₂ with
    | zero =>
      rw [← Affine.Point.zero_def, add_zero, Affine.Point.zero_def, veluPointMap2_zero,
        ← Affine.Point.zero_def, add_zero]
    | some x₂ y₂ h₂ =>

      by_cases hx₂k : x₂ = x₀
      · have hK : veluPointMap2 hchar hQ hgy hΔ (Affine.Point.some x₂ y₂ h₂) = 0 :=
          veluPointMap2_some_of_eq hchar hQ hgy hΔ h₂ hx₂k
        rw [kw_veluPointMap2_add_of_right_ker hchar hQ hgy hΔ hK, hK, add_zero]
      by_cases hx₁k : x₁ = x₀
      · have hK : veluPointMap2 hchar hQ hgy hΔ (Affine.Point.some x₁ y₁ h₁) = 0 :=
          veluPointMap2_some_of_eq hchar hQ hgy hΔ h₁ hx₁k
        rw [add_comm, kw_veluPointMap2_add_of_right_ker hchar hQ hgy hΔ hK, hK, zero_add]

      by_cases hx12 : x₁ = x₂
      · rcases (Affine.Point.X_eq_iff (h₁ := h₂) (h₂ := h₁)).mp hx12.symm with hPeq | hPeq
        · rw [hPeq]; exact kw_veluPointMap2_add_self hchar hQ hgy hΔ htan _
        · rw [hPeq, add_neg_cancel, Affine.Point.zero_def, veluPointMap2_zero,
            ← Affine.Point.zero_def, kw_veluPointMap2_neg hchar hQ hgy hΔ, add_neg_cancel]

      by_cases hsp : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) = x₀
      · have hAns : W.toAffine.Nonsingular
            (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
            (W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂)) :=
          Affine.nonsingular_add h₁ h₂ fun hxy => hx12 hxy.1
        have hK0 : veluPointMap2 hchar hQ hgy hΔ
            ((Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) + .some x₂ y₂ h₂) = 0 := by
          rw [Affine.Point.add_of_X_ne hx12]
          exact veluPointMap2_some_of_eq hchar hQ hgy hΔ hAns hsp
        have hφ1 : veluPointMap2 hchar hQ hgy hΔ (.some x₁ y₁ h₁)
            = -(veluPointMap2 hchar hQ hgy hΔ (.some x₂ y₂ h₂)) := by
          have heq : (Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point)
              = -(.some x₂ y₂ h₂)
                + ((Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) + .some x₂ y₂ h₂) := by abel
          rw [heq, kw_veluPointMap2_add_of_right_ker hchar hQ hgy hΔ hK0,
            kw_veluPointMap2_neg hchar hQ hgy hΔ]
        rw [hK0, hφ1, neg_add_cancel]

      by_cases hsm : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))
          = x₀
      · have h₂' : W.toAffine.Nonsingular x₂ (W.toAffine.negY x₂ y₂) :=
          (Affine.nonsingular_neg ..).mpr h₂
        have hDns : W.toAffine.Nonsingular
            (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)))
            (W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))) :=
          Affine.nonsingular_add h₁ h₂' fun hxy => hx12 hxy.1
        have hKD : veluPointMap2 hchar hQ hgy hΔ
            ((Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) - .some x₂ y₂ h₂) = 0 := by
          rw [sub_eq_add_neg, Affine.Point.neg_some, Affine.Point.add_of_X_ne hx12]
          exact veluPointMap2_some_of_eq hchar hQ hgy hΔ hDns hsm

        have hφeq : veluPointMap2 hchar hQ hgy hΔ (.some x₁ y₁ h₁)
            = veluPointMap2 hchar hQ hgy hΔ (.some x₂ y₂ h₂) := by
          have heq : (Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point)
              = (Affine.Point.some x₂ y₂ h₂ : W.toAffine.Point)
                + ((Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) - .some x₂ y₂ h₂) := by abel
          rw [heq, kw_veluPointMap2_add_of_right_ker hchar hQ hgy hΔ hKD]

        have heq2 : (Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) + .some x₂ y₂ h₂
            = ((Affine.Point.some x₂ y₂ h₂ : W.toAffine.Point) + .some x₂ y₂ h₂)
              + ((Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) - .some x₂ y₂ h₂) := by abel
        rw [heq2, kw_veluPointMap2_add_of_right_ker hchar hQ hgy hΔ hKD,
          kw_veluPointMap2_add_self hchar hQ hgy hΔ htan, hφeq]

      exact kw_veluPointMap2_add_of_secant_diffAvoid hchar hQ hgy hΔ hsec h₁ h₂ hx12 hx₁k
        hx₂k hsp hsm

include hchar hQ hgy hΔ in

theorem kw_veluOrderTwoAddCompatAt_of_carriers
    (hsec : W.KwVeluOrderTwoSecantCompatDiffAvoidAt x₀ y₀)
    (htan : W.KwVeluOrderTwoTangentCompatAt x₀ y₀) :
    W.KwVeluOrderTwoAddCompatAt x₀ y₀ hchar hQ hgy hΔ :=
  kw_veluPointMap2_add' hchar hQ hgy hΔ hsec htan

end Field

end WeierstrassCurve
end Piece_KwVeluOrderTwoAddCompatReduce

section Piece_KwVeluOrderTwoCarrierDischarge
set_option autoImplicit false

noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.slope_of_X_ne a₃ a₁ map Affine.nonsingular_iff mk a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.X_eq_iff Affine.negAddY Affine.Point.zero_def Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.nonsingular_neg Affine.equation_iff_nonsingular Affine.Point.some_ne_zero Δ c₄ Affine.addY Affine.Y_eq_of_X_eq Affine.Point.add_of_X_ne Affine.equation_iff Affine.Point.neg_some Affine.Point.add_self_of_Y_ne Δ' velu2X velu2Y veluPointMap2 veluPointMap2_zero veluPointMap2_some_of_eq veluPointMap2_some_of_ne veluQuotient2 veluQuotient2_a₁ veluQuotient2_a₂ veluQuotient2_a₃ veluQuotient2_a₄ veluGx veluGy veluGy_eq_zero_of_negY_eq veluQuotient2_Delta_eq velu2_secant_negAddY_cleared_identity velu2_tangent_addX_cleared_identity velu2_tangent_negAddY_cleared_identity"
p2m_open "WeierstrassCurve"

theorem kw_veluOrderTwoCarrierDischarge_axiomAnchor : True := by
  have _ := kw_veluOrderTwoAddCompatReduce_axiomAnchor
  have _ := kw_veluOrderTwoSecantConjunctOne_axiomAnchor
  have _ := kw_veluOrderTwoSecantAlign_axiomAnchor
  have _ := kw_veluOrderTwoTangentXAlign_axiomAnchor
  trivial

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} (x₀ y₀ : F)

private abbrev _root_.WeierstrassCurve.KwVeluOrderTwoTangentYAlignAt : Prop :=
  ∀ ⦃x y : F⦄, W.toAffine.Equation x y → y ≠ W.toAffine.negY x y → x ≠ x₀ →
    W.toAffine.addX x x (W.toAffine.slope x x y y) ≠ x₀ →
    W.velu2Y x₀ y₀ x y
      ≠ (W.veluQuotient2 x₀ y₀).toAffine.negY (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y) →
    W.velu2Y x₀ y₀ (W.toAffine.addX x x (W.toAffine.slope x x y y))
        (W.toAffine.addY x x y (W.toAffine.slope x x y y))
      = (W.veluQuotient2 x₀ y₀).toAffine.addY
          (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y)
          ((W.veluQuotient2 x₀ y₀).toAffine.slope (W.velu2X x₀ y₀ x) (W.velu2X x₀ y₀ x)
            (W.velu2Y x₀ y₀ x y) (W.velu2Y x₀ y₀ x y))

p2m_export "WeierstrassCurve" "KwVeluOrderTwoTangentYAlignAt"
variable {x₀ y₀}
variable [W.IsElliptic]
variable (hgy : W.veluGy x₀ y₀ = 0) (hQns : W.toAffine.Nonsingular x₀ y₀)

include hgy hQns in

theorem kw_velu2_tangentCarrier_of_YAlign
    (hYal : W.KwVeluOrderTwoTangentYAlignAt x₀ y₀) :
    W.KwVeluOrderTwoTangentCompatAt x₀ y₀ := by
  have _ := kw_veluOrderTwoCarrierDischarge_axiomAnchor
  intro x y hP hy hx hx2
  have hns := (Affine.equation_iff_nonsingular (W := W.toAffine)).mp hP
  have hY := kw_velu2Y_ne_quotNegY_of_tangent hgy hQns hns hy hx hx2
  exact ⟨hY, kw_velu2_tanX_align hP hQns.1 hgy hy hx hx2 hY, hYal hP hy hx hx2 hY⟩

include hgy hQns in

theorem kw_velu2_secantCarrier :
    W.KwVeluOrderTwoSecantCompatDiffAvoidAt x₀ y₀ := by
  have _ := kw_veluOrderTwoCarrierDischarge_axiomAnchor
  intro x₁ y₁ x₂ y₂ h₁ h₂ hx12 hx₁ hx₂ hsp hsm
  have hns₁ := (Affine.equation_iff_nonsingular (W := W.toAffine)).mp h₁
  have hns₂ := (Affine.equation_iff_nonsingular (W := W.toAffine)).mp h₂
  have hX12 := kw_velu2X_ne_of_diffAvoid hgy hQns hns₁ hns₂ hx12 hx₁ hx₂ hsp hsm
  have hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have h := hgy; rw [veluGy, neg_eq_zero] at h; exact h
  exact ⟨hX12,
    kw_velu2_secX_align h₁ h₂ hQns.1 hord hx12 hx₁ hx₂ hsp hX12,
    kw_velu2_secY_align h₁ h₂ hQns.1 hgy hx12 hx₁ hx₂ hsp hX12⟩

include hgy hQns in

theorem kw_velu2_addCompatAt_of_YAlign
    (hchar : (2 : F) ≠ 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)
    (hYal : W.KwVeluOrderTwoTangentYAlignAt x₀ y₀) :
    W.KwVeluOrderTwoAddCompatAt x₀ y₀ hchar hQns.1 hgy hΔ := by
  have _ := kw_veluOrderTwoCarrierDischarge_axiomAnchor
  exact kw_veluOrderTwoAddCompatAt_of_carriers hchar hQns.1 hgy hΔ
    (kw_velu2_secantCarrier hgy hQns)
    (kw_velu2_tangentCarrier_of_YAlign hgy hQns hYal)

end Field

end WeierstrassCurve

end
end Piece_KwVeluOrderTwoCarrierDischarge

set_option autoImplicit false

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2.WeierstrassCurve.Affine"

theorem solution
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (h2 : (2 : F) ≠ 0) {x₀ y₀ : F} (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) :
    ∃ φ : W.toAffine.Point →+ (W.veluQuotient2 x₀ y₀).toAffine.Point,
      ⇑φ = veluPointMap2 h2 hQ hgy hΔ := by
  have hQns : W.toAffine.Nonsingular x₀ y₀ := W.toAffine.equation_iff_nonsingular.mp hQ
  have hadd : W.KwVeluOrderTwoAddCompatAt x₀ y₀ h2 hQns.1 hgy hΔ :=
    kw_velu2_addCompatAt_of_YAlign hgy hQns h2 hΔ
      (fun _ _ hP hy hx hx2 hY => kw_velu2_tanY_align hP hQns.1 hgy hy hx hx2 hY)
  exact ⟨AddMonoidHom.mk' (veluPointMap2 h2 hQ hgy hΔ) hadd, rfl⟩

end S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2
end P2MW
export P2MW.S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2 (solution)
