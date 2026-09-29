-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_of_levelThreeModulus_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/4963e8fa-9b46-5925-88f7-ec7696bb43f8

import Mathlib
import Definitions.Def_WeierstrassCurve_LevelThreeModulus
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_of_levelThreeModulus_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY VariableChange.mul_def a₃ a₁ map variableChange_a₃ a₂ toAffine Affine.Point Affine.addX Affine.nonsingular_neg variableChange_a₁ VariableChange Affine.equation_iff Affine.Point.neg_some deuringCurve deuringCurve_a₁ deuringCurve_a₃ deuringA₃ tangentSlopeNum tangentSlope flexForm deuringVariableChange levelThreeModulus levelThreeAbscissa levelThreeOrdinate deuringA₃_def flexForm_def deuringVariableChange_u deuringVariableChange_r deuringVariableChange_s deuringVariableChange_t deuringA₃_eq_sub_negY deuringA₃_variableChange flexForm_variableChange tangentSlope_eq_div tangentSlope_eq_slope levelThreeAbscissa_eq_div levelThreeOrdinate_eq_div deuringVariableChange_smul_eq_deuringCurve_levelThreeModulus flexForm_deuringCurve"
namespace LevelThreeDetermines
p2m_open "WeierstrassCurve"

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_variableChange_of_levelThreeModulus_eq.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"

variable {F : Type*} [Field F] [DecidableEq F]

theorem flex_of_three_smul {E : WeierstrassCurve F} {x y : F} (h : E.toAffine.Nonsingular x y)
    (hP : (3 : ℤ) • (Point.some x y h) = 0) : E.deuringA₃ x y ≠ 0 ∧ E.flexForm x y = 0 := by
  have h3 : Point.some x y h + Point.some x y h + Point.some x y h = 0 := by
    rw [← hP, show (3 : ℤ) = 1 + 1 + 1 by norm_num, add_zsmul, add_zsmul, one_zsmul]
  have h2P : Point.some x y h + Point.some x y h = -Point.some x y h := eq_neg_of_add_eq_zero_left h3
  have hy : y ≠ E.toAffine.negY x y := by
    intro hy
    have h0 : Point.some x y h + Point.some x y h = 0 := Point.add_self_of_Y_eq hy
    rw [h0] at h2P
    exact Point.some_ne_zero _ (neg_eq_zero.mp h2P.symm)
  have hΨ : E.deuringA₃ x y ≠ 0 := by rw [deuringA₃_eq_sub_negY]; exact sub_ne_zero.mpr hy
  refine ⟨hΨ, ?_⟩
  rw [Point.add_self_of_Y_ne hy, Affine.Point.neg_some] at h2P
  have hX := (Point.some.inj h2P).1
  rw [← tangentSlope_eq_slope hΨ, Affine.addX] at hX
  have e1 : E.toAffine.a₁ = E.a₁ := rfl
  have e2 : E.toAffine.a₂ = E.a₂ := rfl
  rw [e1, e2] at hX
  have hmd : E.tangentSlope x y * E.deuringA₃ x y = E.tangentSlopeNum x y := by
    rw [tangentSlope_eq_div, div_mul_cancel₀ _ hΨ]
  rw [flexForm_def, ← hmd]
  linear_combination E.deuringA₃ x y ^ 2 * hX

theorem some_congr {W : WeierstrassCurve F} {x₁ y₁ x₂ y₂ : F}
    {h₁ : W.toAffine.Nonsingular x₁ y₁} {h₂ : W.toAffine.Nonsingular x₂ y₂} (hx : x₁ = x₂)
    (hy : y₁ = y₂) : (Point.some x₁ y₁ h₁ : W.toAffine.Point) = Point.some x₂ y₂ h₂ := by
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

theorem nonsingular_of_vc {C : VariableChange F} {W V : WeierstrassCurve F}
    (h : C • W = V) {x y : F} (hW : W.toAffine.Nonsingular (vcX C x) (vcY C x y)) :
    V.toAffine.Nonsingular x y := by
  subst h; exact (nonsingular_variableChange_iff x y).mpr hW

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

theorem vcY_negY {C : VariableChange F} {W V : WeierstrassCurve F} (h : C • W = V) (x y : F) :
    vcY C x (V.toAffine.negY x y) = W.toAffine.negY (vcX C x) (vcY C x y) := by
  subst h
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [vcX, vcY, Affine.negY]
  change (C.u : F) ^ 3 * (-y - (C • W).a₁ * x - (C • W).a₃) + (C.u : F) ^ 2 * C.s * x + C.t = _
  rw [variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
  change _ = -((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) - W.a₁ * ((C.u : F) ^ 2 * x + C.r) - W.a₃
  field_simp
  ring

theorem equivOfVariableChangeEq_neg_some {C : VariableChange F} {W V : WeierstrassCurve F}
    (h : C • W = V) {x y : F} (hV : V.toAffine.Nonsingular x y) :
    equivOfVariableChangeEq h (-.some x y hV) = -equivOfVariableChangeEq h (.some x y hV) := by
  have hV' : V.toAffine.Nonsingular x (V.toAffine.negY x y) := (Affine.nonsingular_neg ..).mpr hV
  rw [Affine.Point.neg_some, equivOfVariableChangeEq_some h hV' (nonsingular_vc h hV'),
    equivOfVariableChangeEq_some h hV (nonsingular_vc h hV), Affine.Point.neg_some]
  exact some_congr rfl (vcY_negY h x y)

section NormalForm

variable (E : WeierstrassCurve F) {x₁ y₁ x₂ y₂ : F}

theorem vc_coords (hΨ : E.deuringA₃ x₁ y₁ ≠ 0) (hx : x₁ ≠ x₂) (u : Fˣ)
    (hu : (u : F) = E.deuringA₃ x₁ y₁ / (x₂ - x₁)) :
    vcX (E.deuringVariableChange x₁ y₁ u) 0 = x₁ ∧
    vcY (E.deuringVariableChange x₁ y₁ u) 0 0 = y₁ ∧
    vcX (E.deuringVariableChange x₁ y₁ u) (E.levelThreeAbscissa x₁ y₁ x₂) = x₂ ∧
    vcY (E.deuringVariableChange x₁ y₁ u) (E.levelThreeAbscissa x₁ y₁ x₂)
      (E.levelThreeOrdinate x₁ y₁ x₂ y₂) = y₂ := by
  have hd : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  refine ⟨by simp [vcX], by simp [vcY], ?_, ?_⟩
  · simp only [vcX, deuringVariableChange_u, deuringVariableChange_r, hu, levelThreeAbscissa_eq_div]
    field_simp
    ring
  · simp only [vcY, deuringVariableChange_u, deuringVariableChange_s, deuringVariableChange_t, hu,
      levelThreeAbscissa_eq_div, levelThreeOrdinate_eq_div]
    field_simp
    ring

theorem normalForm (h₁ : E.toAffine.Nonsingular x₁ y₁) (h₂ : E.toAffine.Nonsingular x₂ y₂)
    (hP₁ : (3 : ℤ) • (Point.some x₁ y₁ h₁) = 0) (hP₂ : (3 : ℤ) • (Point.some x₂ y₂ h₂) = 0)
    (hx : x₁ ≠ x₂) :
    E.levelThreeAbscissa x₁ y₁ x₂ ≠ 0 ∧
    3 * E.levelThreeAbscissa x₁ y₁ x₂ + E.levelThreeModulus x₁ y₁ x₂ ^ 2
          + 3 * E.levelThreeModulus x₁ y₁ x₂ + 3 = 0 ∧
    2 * E.levelThreeOrdinate x₁ y₁ x₂ y₂ + E.levelThreeModulus x₁ y₁ x₂ * E.levelThreeAbscissa x₁ y₁ x₂
          + E.levelThreeAbscissa x₁ y₁ x₂ ≠ 0 ∧
    ∃ κ : VariableChange F,
    ∃ hκ : κ • E = deuringCurve (E.levelThreeModulus x₁ y₁ x₂) (E.levelThreeAbscissa x₁ y₁ x₂),
      (deuringCurve (E.levelThreeModulus x₁ y₁ x₂) (E.levelThreeAbscissa x₁ y₁ x₂)).toAffine.Nonsingular
        0 0 ∧
      (deuringCurve (E.levelThreeModulus x₁ y₁ x₂) (E.levelThreeAbscissa x₁ y₁ x₂)).toAffine.Nonsingular
        (E.levelThreeAbscissa x₁ y₁ x₂) (E.levelThreeOrdinate x₁ y₁ x₂ y₂) ∧
      (∀ (V : WeierstrassCurve F) (hV : κ • E = V) (h₀ : V.toAffine.Nonsingular 0 0),
        Point.equivOfVariableChangeEq hV (.some 0 0 h₀) = .some x₁ y₁ h₁) ∧
      (∀ (V : WeierstrassCurve F) (hV : κ • E = V)
        (h : V.toAffine.Nonsingular (E.levelThreeAbscissa x₁ y₁ x₂) (E.levelThreeOrdinate x₁ y₁ x₂ y₂)),
        Point.equivOfVariableChangeEq hV (.some _ _ h) = .some x₂ y₂ h₂) := by
  obtain ⟨hΨ, hflex⟩ := flex_of_three_smul h₁ hP₁
  obtain ⟨hΨ₂, hflex₂⟩ := flex_of_three_smul h₂ hP₂
  have hd : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hν : E.levelThreeAbscissa x₁ y₁ x₂ ≠ 0 := by
    rw [levelThreeAbscissa_eq_div]
    exact div_ne_zero (pow_ne_zero 3 hd) (pow_ne_zero 2 hΨ)
  have hu0 : E.deuringA₃ x₁ y₁ / (x₂ - x₁) ≠ 0 := div_ne_zero hΨ hd
  set u : Fˣ := Units.mk0 _ hu0 with hu_def
  have hu : (u : F) = E.deuringA₃ x₁ y₁ / (x₂ - x₁) := rfl
  obtain ⟨cX0, cY0, cX2, cY2⟩ := vc_coords E (y₂ := y₂) hΨ hx u hu
  have hκE := deuringVariableChange_smul_eq_deuringCurve_levelThreeModulus h₁.1 hΨ hflex hx u hu
  have hΨw := deuringA₃_variableChange (W := E) (E.deuringVariableChange x₁ y₁ u)
    (E.levelThreeAbscissa x₁ y₁ x₂) (E.levelThreeOrdinate x₁ y₁ x₂ y₂)
  have hw := flexForm_variableChange (W := E) (E.deuringVariableChange x₁ y₁ u)
    (E.levelThreeAbscissa x₁ y₁ x₂) (E.levelThreeOrdinate x₁ y₁ x₂ y₂)
  set κ := E.deuringVariableChange x₁ y₁ u with hκ_def
  set τ := E.levelThreeModulus x₁ y₁ x₂ with hτ_def
  set ν := E.levelThreeAbscissa x₁ y₁ x₂ with hν_def
  set η := E.levelThreeOrdinate x₁ y₁ x₂ y₂ with hη_def
  have hX : (κ.u : F) ^ 2 * ν + κ.r = x₂ := cX2
  have hY : (κ.u : F) ^ 3 * η + (κ.u : F) ^ 2 * κ.s * ν + κ.t = y₂ := cY2
  rw [hX, hY, hκE] at hΨw hw
  have h₀ : (deuringCurve τ ν).toAffine.Nonsingular 0 0 := by
    refine nonsingular_of_vc hκE ?_
    rw [cX0, cY0]; exact h₁
  have h₂' : (deuringCurve τ ν).toAffine.Nonsingular ν η := by
    refine nonsingular_of_vc hκE ?_
    rw [cX2, cY2]; exact h₂

  have hrel : 3 * ν + τ ^ 2 + 3 * τ + 3 = 0 := by
    rw [hflex₂] at hw
    have hfl : (deuringCurve τ ν).flexForm ν η = 0 :=
      (mul_eq_zero.mp hw.symm).resolve_left (pow_ne_zero 8 κ.u.ne_zero)
    rw [flexForm_deuringCurve, show (deuringCurve τ ν).toAffine.polynomial.evalEval ν η = 0 from h₂'.1,
      mul_zero, zero_sub, neg_eq_zero] at hfl
    exact (mul_eq_zero.mp hfl).resolve_left (pow_ne_zero 3 hν)

  have hΨD : 2 * η + τ * ν + ν ≠ 0 := by
    have : (deuringCurve τ ν).deuringA₃ ν η ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hΨw; exact hΨ₂ hΨw
    simpa [deuringA₃_def] using this
  refine ⟨hν, hrel, hΨD, κ, hκE, h₀, h₂', ?_, ?_⟩
  · intro V hV h₀
    rw [equivOfVariableChangeEq_some hV h₀ (nonsingular_vc hV h₀)]
    exact some_congr cX0 cY0
  · intro V hV h
    rw [equivOfVariableChangeEq_some hV h (nonsingular_vc hV h)]
    exact some_congr cX2 cY2

end NormalForm

theorem mainL3 (h3 : (3 : F) ≠ 0) (E E' : WeierstrassCurve F)
    {x₁ y₁ x₂ y₂ : F} (h₁ : E.toAffine.Nonsingular x₁ y₁) (h₂ : E.toAffine.Nonsingular x₂ y₂)
    (hP₁ : (3 : ℤ) • (Point.some x₁ y₁ h₁) = 0) (hP₂ : (3 : ℤ) • (Point.some x₂ y₂ h₂) = 0)
    (hx : x₁ ≠ x₂)
    {x₁' y₁' x₂' y₂' : F} (h₁' : E'.toAffine.Nonsingular x₁' y₁')
    (h₂' : E'.toAffine.Nonsingular x₂' y₂')
    (hP₁' : (3 : ℤ) • (Point.some x₁' y₁' h₁') = 0) (hP₂' : (3 : ℤ) • (Point.some x₂' y₂' h₂') = 0)
    (hx' : x₁' ≠ x₂')
    (hτ : E.levelThreeModulus x₁ y₁ x₂ = E'.levelThreeModulus x₁' y₁' x₂') :
    E.levelThreeAbscissa x₁ y₁ x₂ = E'.levelThreeAbscissa x₁' y₁' x₂' ∧
    (E'.levelThreeOrdinate x₁' y₁' x₂' y₂' = E.levelThreeOrdinate x₁ y₁ x₂ y₂ ∨
      E'.levelThreeOrdinate x₁' y₁' x₂' y₂' = -E.levelThreeOrdinate x₁ y₁ x₂ y₂
        - (E.levelThreeModulus x₁ y₁ x₂ + 1) * E.levelThreeAbscissa x₁ y₁ x₂) ∧
    ∃ γ : VariableChange F, ∃ hγ : γ • E = E',
      Point.equivOfVariableChangeEq hγ (.some x₁' y₁' h₁') = .some x₁ y₁ h₁ ∧
      (Point.equivOfVariableChangeEq hγ (.some x₂' y₂' h₂') = .some x₂ y₂ h₂ ∨
        Point.equivOfVariableChangeEq hγ (.some x₂' y₂' h₂') = -.some x₂ y₂ h₂) ∧
      (E.levelThreeOrdinate x₁ y₁ x₂ y₂ = E'.levelThreeOrdinate x₁' y₁' x₂' y₂' →
        Point.equivOfVariableChangeEq hγ (.some x₂' y₂' h₂') = .some x₂ y₂ h₂) := by
  obtain ⟨hν, hrel, hΨD, κ, hκ, hD₀, hD₂, him₁, him₂⟩ := normalForm E h₁ h₂ hP₁ hP₂ hx
  obtain ⟨hν', hrel', hΨD', κ', hκ', hD₀', hD₂', him₁', him₂'⟩ := normalForm E' h₁' h₂' hP₁' hP₂' hx'
  set τ := E.levelThreeModulus x₁ y₁ x₂ with hτ_def
  set ν := E.levelThreeAbscissa x₁ y₁ x₂ with hν_def
  set η := E.levelThreeOrdinate x₁ y₁ x₂ y₂ with hη_def
  set τ' := E'.levelThreeModulus x₁' y₁' x₂' with hτ'_def
  set ν' := E'.levelThreeAbscissa x₁' y₁' x₂' with hν'_def
  set η' := E'.levelThreeOrdinate x₁' y₁' x₂' y₂' with hη'_def

  have hνν : ν = ν' := by
    have h : (3 : F) * (ν - ν') = 0 := by rw [← hτ] at hrel'; linear_combination hrel - hrel'
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left h3)

  have hκ'' : κ' • E' = deuringCurve τ ν := by rw [hτ, hνν]; exact hκ'

  have heq : η ^ 2 + τ * ν * η + ν * η = ν ^ 3 := by
    have h := (Affine.equation_iff _ _).mp hD₂.1
    simpa [deuringCurve] using h
  have hM₂ : (deuringCurve τ ν).toAffine.Nonsingular ν η' := by rw [hτ, hνν]; exact hD₂'
  have heq' : η' ^ 2 + τ * ν * η' + ν * η' = ν ^ 3 := by
    have h := (Affine.equation_iff _ _).mp hM₂.1
    simpa [deuringCurve] using h
  have hroots : η' = η ∨ η' = -η - (τ + 1) * ν := by
    have h : (η' - η) * (η' - (-η - (τ + 1) * ν)) = 0 := by linear_combination heq' - heq
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  refine ⟨hνν, hroots, ?_⟩

  have hγ : (κ'⁻¹ * κ) • E = E' := by rw [mul_smul, hκ, ← hκ'', inv_smul_smul]
  have hmul : κ' * (κ'⁻¹ * κ) = κ := mul_inv_cancel_left κ' κ
  have hκ₂ : (κ' * (κ'⁻¹ * κ)) • E = deuringCurve τ ν := by rw [hmul]; exact hκ

  have hP₁im : equivOfVariableChangeEq hγ (.some x₁' y₁' h₁') = .some x₁ y₁ h₁ := by
    rw [← him₁' (deuringCurve τ ν) hκ'' hD₀, ← equivOfVariableChangeEq_mul hγ hκ'' hκ₂ hD₀,
      equivOfVariableChangeEq_congr hmul hκ₂ hκ, him₁ (deuringCurve τ ν) hκ hD₀]

  have hM₂' : (deuringCurve τ ν).toAffine.Nonsingular ν' η' := by rw [← hνν]; exact hM₂
  have hP₂'eq : (Point.some x₂' y₂' h₂' : E'.toAffine.Point) =
      equivOfVariableChangeEq hκ'' (.some ν η' hM₂) := by
    rw [← him₂' (deuringCurve τ ν) hκ'' hM₂']
    congr 1
    exact some_congr hνν.symm rfl
  have hP₂im : equivOfVariableChangeEq hγ (.some x₂' y₂' h₂') =
      equivOfVariableChangeEq hκ (.some ν η' hM₂) := by
    rw [hP₂'eq, ← equivOfVariableChangeEq_mul hγ hκ'' hκ₂ hM₂, equivOfVariableChangeEq_congr hmul hκ₂ hκ]

  have hcase₁ : η' = η → equivOfVariableChangeEq hγ (.some x₂' y₂' h₂') = .some x₂ y₂ h₂ := by
    intro he
    rw [hP₂im]
    have hn : (deuringCurve τ ν).toAffine.Nonsingular ν η := hD₂
    rw [show (Point.some ν η' hM₂ : (deuringCurve τ ν).toAffine.Point) = .some ν η hn from
      some_congr rfl he]
    exact him₂ (deuringCurve τ ν) hκ hn
  have hcase₂ : η' = -η - (τ + 1) * ν →
      equivOfVariableChangeEq hγ (.some x₂' y₂' h₂') = -.some x₂ y₂ h₂ := by
    intro he
    rw [hP₂im, ← him₂ (deuringCurve τ ν) hκ hD₂, ← equivOfVariableChangeEq_neg_some hκ hD₂]
    congr 1
    rw [Affine.Point.neg_some]
    apply some_congr rfl
    rw [he]
    change -η - (τ + 1) * ν = -η - (deuringCurve τ ν).a₁ * ν - (deuringCurve τ ν).a₃
    simp only [deuringCurve_a₁, deuringCurve_a₃]
    ring
  refine ⟨κ'⁻¹ * κ, hγ, hP₁im, ?_, ?_⟩
  · rcases hroots with he | he
    · exact Or.inl (hcase₁ he)
    · exact Or.inr (hcase₂ he)
  · intro hee
    rcases hroots with he | he
    · exact hcase₁ he
    ·
      exfalso
      apply hΨD
      change η = η' at hee
      linear_combination hee + he

end WeierstrassCurve.LevelThreeDetermines

open _root_.WeierstrassCurve _root_.P2MW.S_WeierstrassCurve_exists_variableChange_of_levelThreeModulus_eq.WeierstrassCurve WeierstrassCurve.Affine in
theorem solution {F : Type*} [Field F] [DecidableEq F] (h3 : (3 : F) ≠ 0) (E E' : WeierstrassCurve F)
    {x₁ y₁ x₂ y₂ : F} (h₁ : E.toAffine.Nonsingular x₁ y₁) (h₂ : E.toAffine.Nonsingular x₂ y₂)
    (hP₁ : (3 : ℤ) • (Point.some x₁ y₁ h₁) = 0) (hP₂ : (3 : ℤ) • (Point.some x₂ y₂ h₂) = 0)
    (hx : x₁ ≠ x₂)
    {x₁' y₁' x₂' y₂' : F} (h₁' : E'.toAffine.Nonsingular x₁' y₁')
    (h₂' : E'.toAffine.Nonsingular x₂' y₂')
    (hP₁' : (3 : ℤ) • (Point.some x₁' y₁' h₁') = 0) (hP₂' : (3 : ℤ) • (Point.some x₂' y₂' h₂') = 0)
    (hx' : x₁' ≠ x₂')
    (hτ : E.levelThreeModulus x₁ y₁ x₂ = E'.levelThreeModulus x₁' y₁' x₂') :
    E.levelThreeAbscissa x₁ y₁ x₂ = E'.levelThreeAbscissa x₁' y₁' x₂' ∧
    (E'.levelThreeOrdinate x₁' y₁' x₂' y₂' = E.levelThreeOrdinate x₁ y₁ x₂ y₂ ∨
      E'.levelThreeOrdinate x₁' y₁' x₂' y₂' = -E.levelThreeOrdinate x₁ y₁ x₂ y₂
        - (E.levelThreeModulus x₁ y₁ x₂ + 1) * E.levelThreeAbscissa x₁ y₁ x₂) ∧
    ∃ γ : VariableChange F, ∃ hγ : γ • E = E',
      Point.equivOfVariableChangeEq hγ (.some x₁' y₁' h₁') = .some x₁ y₁ h₁ ∧
      (Point.equivOfVariableChangeEq hγ (.some x₂' y₂' h₂') = .some x₂ y₂ h₂ ∨
        Point.equivOfVariableChangeEq hγ (.some x₂' y₂' h₂') = -.some x₂ y₂ h₂) ∧
      (E.levelThreeOrdinate x₁ y₁ x₂ y₂ = E'.levelThreeOrdinate x₁' y₁' x₂' y₂' →
        Point.equivOfVariableChangeEq hγ (.some x₂' y₂' h₂') = .some x₂ y₂ h₂) :=
  WeierstrassCurve.LevelThreeDetermines.mainL3 h3 E E' h₁ h₂ hP₁ hP₂ hx h₁' h₂' hP₁' hP₂' hx' hτ

end S_WeierstrassCurve_exists_variableChange_of_levelThreeModulus_eq
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_of_levelThreeModulus_eq (solution)
