-- Prove2me | solution 1 for WeierstrassCurve.Affine.Point.vcInvFun_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/8622b831-aaa8-55ed-a946-76a535fd5d90

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_Point_vcInvFun_add

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ a₁ map variableChange_a₃ a₄ a₂ variableChange_a₂ toAffine Affine.Point variableChange_a₁ variableChange_a₄ VariableChange Affine.Point.vcInvFun"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY slope_of_X_ne slope map Point.some Nonsingular negAddY slope_of_Y_ne Point addX addY Y_eq_of_X_eq vcX vcY Point.vcInvFun"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

variable {K : Type*} [Field K]

section Formulas

variable (C : VariableChange K) (W : WeierstrassCurve.Affine K)

variable {C W}

theorem vcAdd_u_ne_zero : (C.u : K) ≠ 0 := C.u.ne_zero

theorem vcX_injective : Function.Injective (vcX C) := by
  intro a b h
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [vcX] at h
  have : (C.u : K) ^ 2 * a = (C.u : K) ^ 2 * b := by linear_combination h
  exact mul_left_cancel₀ (pow_ne_zero 2 hu) this

theorem vcY_injective (x' : K) : Function.Injective (vcY C x') := by
  intro a b h
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [vcY] at h
  have : (C.u : K) ^ 3 * a = (C.u : K) ^ 3 * b := by linear_combination h
  exact mul_left_cancel₀ (pow_ne_zero 3 hu) this

theorem vcAdd_partialX_aux (x' y' : K) :
    W.a₁ * vcY C x' y' - (3 * vcX C x' ^ 2 + 2 * W.a₂ * vcX C x' + W.a₄)
      + C.s * (2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃)
    = (C.u : K) ^ 4 *
      ((C • W).a₁ * y' - (3 * x' ^ 2 + 2 * (C • W).a₂ * x' + (C • W).a₄)) := by
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₂, variableChange_a₄,
    Units.val_inv_eq_inv_val]
  field_simp; ring

theorem vcAdd_partialY_aux (x' y' : K) :
    2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃
      = (C.u : K) ^ 3 * (2 * y' + (C • W).a₁ * x' + (C • W).a₃) := by
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp; ring

theorem negY_variableChange (x' y' : K) :
    W.negY (vcX C x') (vcY C x' y') = vcY C x' ((C • W).toAffine.negY x' y') := by
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [negY, vcX, vcY, variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

theorem Yeq_variableChange_iff (x₁' x₂' y₁' y₂' : K) :
    (vcX C x₁' = vcX C x₂' ∧ vcY C x₁' y₁' = W.negY (vcX C x₂') (vcY C x₂' y₂'))
      ↔ (x₁' = x₂' ∧ y₁' = (C • W).toAffine.negY x₂' y₂') := by
  constructor
  · rintro ⟨hx, hy⟩
    have hx' : x₁' = x₂' := vcX_injective hx
    subst hx'
    refine ⟨rfl, ?_⟩
    rw [negY_variableChange x₁' y₂'] at hy
    exact vcY_injective x₁' hy
  · rintro ⟨hx, hy⟩
    subst hx
    exact ⟨rfl, by rw [negY_variableChange x₁' y₂', hy]⟩

theorem slope_variableChange [DecidableEq K] (x₁' x₂' y₁' y₂' : K)
    (h₁ : (C • W).toAffine.Equation x₁' y₁') (h₂ : (C • W).toAffine.Equation x₂' y₂')
    (hxy : ¬(x₁' = x₂' ∧ y₁' = (C • W).toAffine.negY x₂' y₂')) :
    W.slope (vcX C x₁') (vcX C x₂') (vcY C x₁' y₁') (vcY C x₂' y₂')
      = (C.u : K) * (C • W).toAffine.slope x₁' x₂' y₁' y₂' + C.s := by
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  by_cases hx : x₁' = x₂'
  · have hy : y₁' ≠ (C • W).toAffine.negY x₂' y₂' := fun h => hxy ⟨hx, h⟩
    have hyy : y₁' = y₂' := (Y_eq_of_X_eq h₁ h₂ hx).resolve_right hy
    subst hx
    subst hyy
    have hyW : vcY C x₁' y₁' ≠ W.negY (vcX C x₁') (vcY C x₁' y₁') := by
      intro h
      exact hy ((Yeq_variableChange_iff x₁' x₁' y₁' y₁').mp ⟨rfl, h⟩).2
    rw [slope_of_Y_ne rfl hyW, slope_of_Y_ne rfl hy]
    have hd : vcY C x₁' y₁' - W.negY (vcX C x₁') (vcY C x₁' y₁')
        = (C.u : K) ^ 3 * (y₁' - (C • W).toAffine.negY x₁' y₁') := by
      rw [negY_variableChange x₁' y₁']
      simp only [vcY]
      ring
    have hPYden : y₁' - (C • W).toAffine.negY x₁' y₁'
        = 2 * y₁' + (C • W).a₁ * x₁' + (C • W).a₃ := by
      simp only [negY]
      ring
    have hn : 3 * vcX C x₁' ^ 2 + 2 * W.a₂ * vcX C x₁' + W.a₄ - W.a₁ * vcY C x₁' y₁'
        = (C.u : K) ^ 4 * (3 * x₁' ^ 2 + 2 * (C • W).a₂ * x₁'
            + (C • W).a₄ - (C • W).a₁ * y₁')
          + C.s * ((C.u : K) ^ 3 * (y₁' - (C • W).toAffine.negY x₁' y₁')) := by
      have hX := vcAdd_partialX_aux (C := C) (W := W) x₁' y₁'
      have hY := vcAdd_partialY_aux (C := C) (W := W) x₁' y₁'
      rw [hPYden]
      linear_combination (-1 : K) * hX + C.s * hY
    have hden' : y₁' - (C • W).toAffine.negY x₁' y₁' ≠ 0 := sub_ne_zero_of_ne hy
    rw [hd, hn]
    field_simp
  · have hxW : vcX C x₁' ≠ vcX C x₂' := fun h => hx (vcX_injective h)
    rw [slope_of_X_ne hxW, slope_of_X_ne hx]
    have hd : vcX C x₁' - vcX C x₂' = (C.u : K) ^ 2 * (x₁' - x₂') := by
      simp only [vcX]; ring
    have hn : vcY C x₁' y₁' - vcY C x₂' y₂'
        = (C.u : K) ^ 3 * (y₁' - y₂') + (C.u : K) ^ 2 * C.s * (x₁' - x₂') := by
      simp only [vcY]; ring
    rw [hd, hn]
    have hxne : x₁' - x₂' ≠ 0 := sub_ne_zero_of_ne hx
    field_simp

theorem addX_variableChange (x₁' x₂' L : K) :
    W.addX (vcX C x₁') (vcX C x₂') ((C.u : K) * L + C.s)
      = vcX C ((C • W).toAffine.addX x₁' x₂' L) := by
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [addX, vcX, variableChange_a₁, variableChange_a₂, Units.val_inv_eq_inv_val]
  field_simp
  ring

theorem addY_variableChange (x₁' x₂' y₁' L : K) :
    W.addY (vcX C x₁') (vcX C x₂') (vcY C x₁' y₁') ((C.u : K) * L + C.s)
      = vcY C ((C • W).toAffine.addX x₁' x₂' L) ((C • W).toAffine.addY x₁' x₂' y₁' L) := by
  have hu : (C.u : K) ≠ 0 := vcAdd_u_ne_zero
  simp only [addY, negAddY, addX, negY, vcX, vcY, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

end Formulas

namespace Point
p2m_export "WeierstrassCurve.Affine.Point" "add_of_Y_eq some add_some map vcFun vcInvFun vcFun_zero vcFun_leftInverse vcFun_rightInverse"
p2m_open "WeierstrassCurve.Affine.Point"

variable {C : VariableChange K} {W : WeierstrassCurve.Affine K}

theorem some_of_eq_of_eq' {V : WeierstrassCurve.Affine K} {x₁ y₁ x₂ y₂ : K}
    {h₁ : V.Nonsingular x₁ y₁} {h₂ : V.Nonsingular x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : V.Point) = Point.some x₂ y₂ h₂ := by
  subst hx
  subst hy
  rfl

variable [DecidableEq K]

theorem vcFun_add (P Q : (C • W).toAffine.Point) :
    vcFun C W (P + Q) = vcFun C W P + vcFun C W Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rfl
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
  · rw [add_of_Y_eq hxy.1 hxy.2, vcFun_zero]
    show (0 : W.Point) = Point.some (vcX C x₁) (vcY C x₁ y₁) _ + Point.some (vcX C x₂) (vcY C x₂ y₂) _
    have hxyW := (Yeq_variableChange_iff (W := W) x₁ x₂ y₁ y₂).mpr hxy
    exact (add_of_Y_eq hxyW.1 hxyW.2).symm
  · have hxyW : ¬(vcX C x₁ = vcX C x₂ ∧ vcY C x₁ y₁ = W.negY (vcX C x₂) (vcY C x₂ y₂)) :=
      fun h => hxy ((Yeq_variableChange_iff x₁ x₂ y₁ y₂).mp h)
    have hslope := slope_variableChange (W := W) x₁ x₂ y₁ y₂ h₁.1 h₂.1 hxy
    rw [add_some hxy]
    show Point.some _ _ _ = Point.some (vcX C x₁) (vcY C x₁ y₁) _ + Point.some (vcX C x₂) (vcY C x₂ y₂) _
    rw [add_some hxyW]
    refine some_of_eq_of_eq' ?_ ?_
    · rw [hslope, addX_variableChange]
    · rw [hslope, addY_variableChange]

theorem vcInvFun_add' (P Q : W.Point) :
    vcInvFun C W (P + Q) = vcInvFun C W P + vcInvFun C W Q := by
  apply vcFun_leftInverse.injective
  rw [vcFun_add, vcFun_rightInverse P, vcFun_rightInverse Q, vcFun_rightInverse (P + Q)]

end Point

end WeierstrassCurve.Affine

theorem solution {K : Type*} [Field K] [DecidableEq K]
    (C : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve.Affine K) (P Q : W.Point) :
    WeierstrassCurve.Affine.Point.vcInvFun C W (P + Q) =
      WeierstrassCurve.Affine.Point.vcInvFun C W P + WeierstrassCurve.Affine.Point.vcInvFun C W Q :=
  WeierstrassCurve.Affine.Point.vcInvFun_add' P Q

end S_WeierstrassCurve_Affine_Point_vcInvFun_add
end P2MW
export P2MW.S_WeierstrassCurve_Affine_Point_vcInvFun_add (solution)
