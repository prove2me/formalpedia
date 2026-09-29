-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_of_legendreLambda_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/0b68166f-886a-535e-8641-813864ae43e6

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_WeierstrassCurve_LegendreModulus
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_of_legendreLambda_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine VariableChange.mul_def a₃ a₁ map b₂ variableChange_a₃ a₄ a₂ a₆ variableChange_a₆ variableChange_a₂ toAffine Affine.Point b₆ b₈ variableChange_a₁ variableChange_a₄ Δ VariableChange Affine.equation_iff b₄ legendreCurve thirdTwoTorsionX legendreLambda legendreVariableChange legendreVariableChange_u legendreVariableChange_r legendreVariableChange_s legendreVariableChange_t"
namespace LegendreDetermines
p2m_open "WeierstrassCurve"

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_variableChange_of_legendreLambda_eq.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"

variable {F : Type*} [Field F]

def mCurve (d₂ d₃ : F) : WeierstrassCurve F := ⟨0, -(d₂ + d₃), 0, d₂ * d₃, 0⟩

theorem mCurve_one (t : F) : mCurve 1 t = legendreCurve t := by
  simp only [mCurve, legendreCurve, one_mul]

theorem quad_rel (E : WeierstrassCurve F) {x₁ x₂ : F} (hx : x₁ ≠ x₂)
    (hr₁ : 4 * x₁ ^ 3 + E.b₂ * x₁ ^ 2 + 2 * E.b₄ * x₁ + E.b₆ = 0)
    (hr₂ : 4 * x₂ ^ 3 + E.b₂ * x₂ ^ 2 + 2 * E.b₄ * x₂ + E.b₆ = 0) :
    4 * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2) + E.b₂ * (x₁ + x₂) + 2 * E.b₄ = 0 := by
  have hne : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  apply mul_left_cancel₀ hne
  linear_combination hr₂ - hr₁

theorem legendreVariableChange_smul (h2 : (2 : F) ≠ 0) (E : WeierstrassCurve F) {x₁ x₂ w : F}
    (hw : w ≠ 0) (hx : x₁ ≠ x₂)
    (hr₁ : 4 * x₁ ^ 3 + E.b₂ * x₁ ^ 2 + 2 * E.b₄ * x₁ + E.b₆ = 0)
    (hr₂ : 4 * x₂ ^ 3 + E.b₂ * x₂ ^ 2 + 2 * E.b₄ * x₂ + E.b₆ = 0) :
    E.legendreVariableChange x₁ w hw • E =
      mCurve ((x₂ - x₁) / w ^ 2) ((E.thirdTwoTorsionX x₁ x₂ - x₁) / w ^ 2) := by
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hq := quad_rel E hx hr₁ hr₂
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hq hr₁
  ext
  ·
    simp only [mCurve, variableChange_a₁, legendreVariableChange, Units.val_inv_eq_inv_val,
      Units.val_mk0]
    field_simp
    ring
  ·
    simp only [mCurve, thirdTwoTorsionX, WeierstrassCurve.b₂, variableChange_a₂,
      legendreVariableChange, Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
    ring
  ·
    simp only [mCurve, variableChange_a₃, legendreVariableChange, Units.val_inv_eq_inv_val,
      Units.val_mk0]
    field_simp
    ring
  ·
    simp only [mCurve, thirdTwoTorsionX, WeierstrassCurve.b₂, variableChange_a₄,
      legendreVariableChange, Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
    linear_combination 2 * hq
  ·
    simp only [mCurve, variableChange_a₆, legendreVariableChange, Units.val_inv_eq_inv_val,
      Units.val_mk0]
    field_simp
    linear_combination hr₁

section TwoTorsion

variable [DecidableEq F]

theorem two_mul_y_eq {E : WeierstrassCurve F} {x y : F} (h : E.toAffine.Nonsingular x y)
    (hP : (2 : ℤ) • (Point.some x y h) = 0) : 2 * y + E.a₁ * x + E.a₃ = 0 := by
  rw [two_zsmul, add_eq_zero_iff_eq_neg, neg_some, some.injEq] at hP
  have hy := hP.2
  simp only [negY] at hy
  linear_combination hy

theorem twoTorsion_root {E : WeierstrassCurve F} {x y : F} (h : E.toAffine.Nonsingular x y)
    (hP : (2 : ℤ) • (Point.some x y h) = 0) : 4 * x ^ 3 + E.b₂ * x ^ 2 + 2 * E.b₄ * x + E.b₆ = 0 := by
  have hy := two_mul_y_eq h hP
  have heq := h.left
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination -4 * heq + (2 * y + E.a₁ * x + E.a₃) * hy

end TwoTorsion

section PointMap

variable [DecidableEq F]

theorem some_congr {W : WeierstrassCurve F} {x₁ y₁ x₂ y₂ : F}
    {h₁ : W.toAffine.Nonsingular x₁ y₁} {h₂ : W.toAffine.Nonsingular x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : W.toAffine.Point) = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

theorem equivOfVariableChangeEq_some {C : VariableChange F} {W V : WeierstrassCurve F}
    (h : C • W = V) {x y : F} (hV : V.toAffine.Nonsingular x y)
    (hW : W.toAffine.Nonsingular (vcX C x) (vcY C x y)) :
    equivOfVariableChangeEq h (.some x y hV) = .some _ _ hW := by
  subst h; rfl

theorem nonsingular_vc {C : VariableChange F} {W V : WeierstrassCurve F}
    (h : C • W = V) {x y : F} (hV : V.toAffine.Nonsingular x y) :
    W.toAffine.Nonsingular (vcX C x) (vcY C x y) := by
  subst h; exact (nonsingular_variableChange_iff x y).mp hV

theorem equivOfVariableChangeEq_congr {C C' : VariableChange F} {W V : WeierstrassCurve F}
    (hC : C = C') (h : C • W = V) (h' : C' • W = V) :
    equivOfVariableChangeEq h = equivOfVariableChangeEq h' := by
  subst hC; rfl

theorem equivOfVariableChangeEq_mul {C₁ C₂ : VariableChange F} {W V U : WeierstrassCurve F}
    (h₁ : C₁ • W = V) (h₂ : C₂ • V = U) (h : (C₂ * C₁) • W = U) {x y : F}
    (hU : U.toAffine.Nonsingular x y) :
    equivOfVariableChangeEq h (.some x y hU) =
      equivOfVariableChangeEq h₁ (equivOfVariableChangeEq h₂ (.some x y hU)) := by
  have hV := nonsingular_vc h₂ hU
  have hW := nonsingular_vc h₁ hV
  have hW' := nonsingular_vc h hU
  rw [equivOfVariableChangeEq_some h₂ hU hV, equivOfVariableChangeEq_some h₁ hV hW,
    equivOfVariableChangeEq_some h hU hW']
  apply some_congr
  · simp only [vcX, VariableChange.mul_def, Units.val_mul]; ring
  · simp only [vcX, vcY, VariableChange.mul_def, Units.val_mul]; ring

end PointMap

section Legendre

variable [DecidableEq F]

theorem legendre_Δ (l : F) : (legendreCurve l).Δ = 16 * l ^ 2 * (l - 1) ^ 2 := by
  simp only [legendreCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem legendreVariableChange_image₁ (h2 : (2 : F) ≠ 0) {E V : WeierstrassCurve F} {x₁ y₁ w : F}
    (hw : w ≠ 0) (h₁ : E.toAffine.Nonsingular x₁ y₁) (hy₁ : 2 * y₁ + E.a₁ * x₁ + E.a₃ = 0)
    (hV : E.legendreVariableChange x₁ w hw • E = V) (h₀ : V.toAffine.Nonsingular 0 0) :
    equivOfVariableChangeEq hV (.some 0 0 h₀) = .some x₁ y₁ h₁ := by
  rw [equivOfVariableChangeEq_some hV h₀ (nonsingular_vc hV h₀)]
  apply some_congr
  · simp [vcX]
  · simp only [vcY, legendreVariableChange_u, legendreVariableChange_s, legendreVariableChange_t]
    field_simp
    linear_combination -hy₁

theorem legendreVariableChange_image₂ (h2 : (2 : F) ≠ 0) {E V : WeierstrassCurve F}
    {x₁ x₂ y₂ w d : F} (hw : w ≠ 0) (h₂ : E.toAffine.Nonsingular x₂ y₂)
    (hy₂ : 2 * y₂ + E.a₁ * x₂ + E.a₃ = 0) (hd : w ^ 2 * d = x₂ - x₁)
    (hV : E.legendreVariableChange x₁ w hw • E = V) (h₀ : V.toAffine.Nonsingular d 0) :
    equivOfVariableChangeEq hV (.some d 0 h₀) = .some x₂ y₂ h₂ := by
  rw [equivOfVariableChangeEq_some hV h₀ (nonsingular_vc hV h₀)]
  apply some_congr
  · simp only [vcX, legendreVariableChange_u, legendreVariableChange_r, hd]; ring
  · simp only [vcY, legendreVariableChange_u, legendreVariableChange_s, legendreVariableChange_t]
    rw [show w ^ 3 * (0 : F) + w ^ 2 * (-E.a₁ / 2) * d = (x₂ - x₁) * (-E.a₁ / 2) by rw [← hd]; ring]
    field_simp
    linear_combination -hy₂

theorem nonsingular_image₁ (h2 : (2 : F) ≠ 0) {E V : WeierstrassCurve F} {x₁ y₁ w : F}
    (hw : w ≠ 0) (h₁ : E.toAffine.Nonsingular x₁ y₁) (hy₁ : 2 * y₁ + E.a₁ * x₁ + E.a₃ = 0)
    (hV : E.legendreVariableChange x₁ w hw • E = V) : V.toAffine.Nonsingular 0 0 := by
  subst hV
  refine (nonsingular_variableChange_iff 0 0).mpr ?_
  convert h₁ using 1
  · simp [vcX]
  · simp only [vcY, legendreVariableChange_u, legendreVariableChange_s, legendreVariableChange_t]
    field_simp
    linear_combination -hy₁

theorem nonsingular_image₂ (h2 : (2 : F) ≠ 0) {E V : WeierstrassCurve F} {x₁ x₂ y₂ w d : F}
    (hw : w ≠ 0) (h₂ : E.toAffine.Nonsingular x₂ y₂) (hy₂ : 2 * y₂ + E.a₁ * x₂ + E.a₃ = 0)
    (hd : w ^ 2 * d = x₂ - x₁) (hV : E.legendreVariableChange x₁ w hw • E = V) :
    V.toAffine.Nonsingular d 0 := by
  subst hV
  refine (nonsingular_variableChange_iff d 0).mpr ?_
  convert h₂ using 1
  · simp only [vcX, legendreVariableChange_u, legendreVariableChange_r, hd]; ring
  · simp only [vcY, legendreVariableChange_u, legendreVariableChange_s, legendreVariableChange_t]
    rw [show w ^ 3 * (0 : F) + w ^ 2 * (-E.a₁ / 2) * d = (x₂ - x₁) * (-E.a₁ / 2) by rw [← hd]; ring]
    field_simp
    linear_combination -hy₂

theorem mainL2 (h2 : (2 : F) ≠ 0) (E E' : WeierstrassCurve F)
    {x₁ y₁ x₂ y₂ : F} (h₁ : E.toAffine.Nonsingular x₁ y₁) (h₂ : E.toAffine.Nonsingular x₂ y₂)
    (hP₁ : (2 : ℤ) • (Point.some x₁ y₁ h₁) = 0) (hP₂ : (2 : ℤ) • (Point.some x₂ y₂ h₂) = 0)
    (hx : x₁ ≠ x₂)
    {x₁' y₁' x₂' y₂' : F} (h₁' : E'.toAffine.Nonsingular x₁' y₁')
    (h₂' : E'.toAffine.Nonsingular x₂' y₂')
    (hP₁' : (2 : ℤ) • (Point.some x₁' y₁' h₁') = 0) (hP₂' : (2 : ℤ) • (Point.some x₂' y₂' h₂') = 0)
    (hx' : x₁' ≠ x₂') {u : F} (hu : u ^ 2 * (x₂' - x₁') = x₂ - x₁)
    (hlam : E.legendreLambda x₁ x₂ = E'.legendreLambda x₁' x₂') :
    ∃ γ : VariableChange F, ∃ hγ : γ • E = E',
      equivOfVariableChangeEq hγ (.some x₁' y₁' h₁') = .some x₁ y₁ h₁ ∧
      equivOfVariableChangeEq hγ (.some x₂' y₂' h₂') = .some x₂ y₂ h₂ := by
  have hy₁ := two_mul_y_eq h₁ hP₁
  have hy₂ := two_mul_y_eq h₂ hP₂
  have hy₁' := two_mul_y_eq h₁' hP₁'
  have hy₂' := two_mul_y_eq h₂' hP₂'
  have hne : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hne' : x₂' - x₁' ≠ 0 := sub_ne_zero.mpr (Ne.symm hx')
  have hu0 : u ≠ 0 := by
    rintro rfl; apply hne; rw [← hu]; ring
  have hui : u⁻¹ ≠ 0 := inv_ne_zero hu0

  have hd₃ : (E'.thirdTwoTorsionX x₁' x₂' - x₁') * u ^ 2 = E.thirdTwoTorsionX x₁ x₂ - x₁ := by
    have h := hlam
    rw [legendreLambda, legendreLambda, div_eq_div_iff hne hne'] at h
    apply mul_right_cancel₀ hne'
    linear_combination (E'.thirdTwoTorsionX x₁' x₂' - x₁') * hu - h

  have hκ : E.legendreVariableChange x₁ 1 one_ne_zero • E =
      mCurve (x₂ - x₁) (E.thirdTwoTorsionX x₁ x₂ - x₁) := by
    rw [legendreVariableChange_smul h2 E one_ne_zero hx (twoTorsion_root h₁ hP₁)
      (twoTorsion_root h₂ hP₂)]
    simp
  have hκ' : E'.legendreVariableChange x₁' u⁻¹ hui • E' =
      mCurve (x₂ - x₁) (E.thirdTwoTorsionX x₁ x₂ - x₁) := by
    rw [legendreVariableChange_smul h2 E' hui hx' (twoTorsion_root h₁' hP₁')
      (twoTorsion_root h₂' hP₂')]
    congr 1
    · rw [← hu]; field_simp
    · rw [← hd₃]; field_simp
  set κ := E.legendreVariableChange x₁ 1 one_ne_zero with hκdef
  set κ' := E'.legendreVariableChange x₁' u⁻¹ hui with hκ'def
  have hγ : (κ'⁻¹ * κ) • E = E' := by rw [mul_smul, hκ, ← hκ', inv_smul_smul]
  refine ⟨κ'⁻¹ * κ, hγ, ?_, ?_⟩
  · have hmul : κ' * (κ'⁻¹ * κ) = κ := mul_inv_cancel_left κ' κ
    have hM : (mCurve (x₂ - x₁) (E.thirdTwoTorsionX x₁ x₂ - x₁)).toAffine.Nonsingular 0 0 :=
      nonsingular_image₁ h2 hui h₁' hy₁' hκ'
    have him' : equivOfVariableChangeEq hκ' (.some 0 0 hM) = .some x₁' y₁' h₁' :=
      legendreVariableChange_image₁ h2 hui h₁' hy₁' hκ' hM
    have him : equivOfVariableChangeEq hκ (.some 0 0 hM) = .some x₁ y₁ h₁ :=
      legendreVariableChange_image₁ h2 one_ne_zero h₁ hy₁ hκ hM
    have hκ₂ : (κ' * (κ'⁻¹ * κ)) • E = mCurve (x₂ - x₁) (E.thirdTwoTorsionX x₁ x₂ - x₁) := by
      rw [hmul]; exact hκ
    rw [← him', ← equivOfVariableChangeEq_mul hγ hκ' hκ₂ hM,
      equivOfVariableChangeEq_congr hmul hκ₂ hκ, him]
  · have hmul : κ' * (κ'⁻¹ * κ) = κ := mul_inv_cancel_left κ' κ
    have hdd : (1 : F) ^ 2 * (x₂ - x₁) = x₂ - x₁ := by ring
    have hdd' : (u⁻¹) ^ 2 * (x₂ - x₁) = x₂' - x₁' := by rw [← hu]; field_simp
    have hM : (mCurve (x₂ - x₁) (E.thirdTwoTorsionX x₁ x₂ - x₁)).toAffine.Nonsingular (x₂ - x₁) 0 :=
      nonsingular_image₂ h2 hui h₂' hy₂' hdd' hκ'
    have him' : equivOfVariableChangeEq hκ' (.some (x₂ - x₁) 0 hM) = .some x₂' y₂' h₂' :=
      legendreVariableChange_image₂ h2 hui h₂' hy₂' hdd' hκ' hM
    have him : equivOfVariableChangeEq hκ (.some (x₂ - x₁) 0 hM) = .some x₂ y₂ h₂ :=
      legendreVariableChange_image₂ h2 one_ne_zero h₂ hy₂ hdd hκ hM
    have hκ₂ : (κ' * (κ'⁻¹ * κ)) • E = mCurve (x₂ - x₁) (E.thirdTwoTorsionX x₁ x₂ - x₁) := by
      rw [hmul]; exact hκ
    rw [← him', ← equivOfVariableChangeEq_mul hγ hκ' hκ₂ hM,
      equivOfVariableChangeEq_congr hmul hκ₂ hκ, him]

end Legendre

end WeierstrassCurve.LegendreDetermines

open _root_.WeierstrassCurve _root_.P2MW.S_WeierstrassCurve_exists_variableChange_of_legendreLambda_eq.WeierstrassCurve WeierstrassCurve.Affine in
theorem solution {F : Type*} [Field F] [DecidableEq F] (h2 : (2 : F) ≠ 0) (E E' : WeierstrassCurve F) {x₁ y₁ x₂ y₂ : F} (h₁ : E.toAffine.Nonsingular x₁ y₁) (h₂ : E.toAffine.Nonsingular x₂ y₂) (hP₁ : (2 : ℤ) • (Point.some x₁ y₁ h₁) = 0) (hP₂ : (2 : ℤ) • (Point.some x₂ y₂ h₂) = 0) (hx : x₁ ≠ x₂) {x₁' y₁' x₂' y₂' : F} (h₁' : E'.toAffine.Nonsingular x₁' y₁') (h₂' : E'.toAffine.Nonsingular x₂' y₂') (hP₁' : (2 : ℤ) • (Point.some x₁' y₁' h₁') = 0) (hP₂' : (2 : ℤ) • (Point.some x₂' y₂' h₂') = 0) (hx' : x₁' ≠ x₂') {u : F} (hu : u ^ 2 * (x₂' - x₁') = x₂ - x₁) (hl : E.legendreLambda x₁ x₂ = E'.legendreLambda x₁' x₂') :
    ∃ γ : VariableChange F, ∃ hγ : γ • E = E',
      Point.equivOfVariableChangeEq hγ (.some x₁' y₁' h₁') = .some x₁ y₁ h₁ ∧
      Point.equivOfVariableChangeEq hγ (.some x₂' y₂' h₂') = .some x₂ y₂ h₂ :=
  WeierstrassCurve.LegendreDetermines.mainL2 h2 E E' h₁ h₂ hP₁ hP₂ hx h₁' h₂' hP₁' hP₂' hx' hu hl

end S_WeierstrassCurve_exists_variableChange_of_legendreLambda_eq
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_of_legendreLambda_eq (solution)
