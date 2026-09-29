-- Prove2me | solution 1 for WeierstrassCurve.exists_map_residue_eq_and_reduceHom_comp_eq_of_variableChange_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/35029b34-6646-57e4-bca4-1a47ba806a40

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_PointAddEquivOfEq
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_map_residue_eq_and_reduceHom_comp_eq_of_variableChange_smul_eq

set_option autoImplicit false

open IsLocalRing Polynomial
open scoped Polynomial.Bivariate

namespace RigidificationA

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

section VCAdd

variable {K : Type*} [Field K] {C : VariableChange K} {W : WeierstrassCurve.Affine K}

private lemma u_ne_zero' : (C.u : K) ≠ 0 := C.u.ne_zero

lemma vcX_injective : Function.Injective (vcX C) := by
  intro a b h
  have hu : (C.u : K) ≠ 0 := u_ne_zero'
  have h' : (C.u : K) ^ 2 * a = (C.u : K) ^ 2 * b := by
    have := h; simp only [vcX] at this; linear_combination this
  exact mul_left_cancel₀ (pow_ne_zero 2 hu) h'

lemma vcY_injective (x' : K) : Function.Injective (vcY C x') := by
  intro a b h
  have hu : (C.u : K) ≠ 0 := u_ne_zero'
  have h' : (C.u : K) ^ 3 * a = (C.u : K) ^ 3 * b := by
    have := h; simp only [vcY] at this; linear_combination this
  exact mul_left_cancel₀ (pow_ne_zero 3 hu) h'

private lemma partialX_aux' (x' y' : K) :
    W.a₁ * vcY C x' y' - (3 * vcX C x' ^ 2 + 2 * W.a₂ * vcX C x' + W.a₄)
      + C.s * (2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃)
    = (C.u : K) ^ 4 *
      ((C • W).a₁ * y' - (3 * x' ^ 2 + 2 * (C • W).a₂ * x' + (C • W).a₄)) := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero'
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₂, variableChange_a₄,
    Units.val_inv_eq_inv_val]
  field_simp; ring

private lemma partialY_aux' (x' y' : K) :
    2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃
      = (C.u : K) ^ 3 * (2 * y' + (C • W).a₁ * x' + (C • W).a₃) := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero'
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp; ring

lemma negY_variableChange (x' y' : K) :
    W.negY (vcX C x') (vcY C x' y') = vcY C x' ((C • W).toAffine.negY x' y') := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero'
  simp only [negY, vcX, vcY, variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

lemma Yeq_variableChange_iff (x₁' x₂' y₁' y₂' : K) :
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

lemma slope_variableChange [DecidableEq K] (x₁' x₂' y₁' y₂' : K)
    (h₁ : (C • W).toAffine.Equation x₁' y₁') (h₂ : (C • W).toAffine.Equation x₂' y₂')
    (hxy : ¬(x₁' = x₂' ∧ y₁' = (C • W).toAffine.negY x₂' y₂')) :
    W.slope (vcX C x₁') (vcX C x₂') (vcY C x₁' y₁') (vcY C x₂' y₂')
      = (C.u : K) * (C • W).toAffine.slope x₁' x₂' y₁' y₂' + C.s := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero'
  by_cases hx : x₁' = x₂'
  · have hy : y₁' ≠ (C • W).toAffine.negY x₂' y₂' := fun h => hxy ⟨hx, h⟩
    have hyy : y₁' = y₂' := (Y_eq_of_X_eq h₁ h₂ hx).resolve_right hy
    subst hx
    subst hyy
    have hyW : vcY C x₁' y₁' ≠ W.negY (vcX C x₁') (vcY C x₁' y₁') := by
      intro h
      exact hy ((Yeq_variableChange_iff x₁' x₁' y₁' y₁').mp ⟨rfl, h⟩).2
    rw [slope_of_Y_ne rfl hyW, slope_of_Y_ne rfl hy]
    have hden' : y₁' - (C • W).toAffine.negY x₁' y₁' ≠ 0 := sub_ne_zero_of_ne hy
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
      have hX := partialX_aux' (C := C) (W := W) x₁' y₁'
      have hY := partialY_aux' (C := C) (W := W) x₁' y₁'
      rw [hPYden]
      linear_combination (-1 : K) * hX + C.s * hY
    rw [hd, hn]
    have h3 : (C.u : K) ^ 3 * (y₁' - (C • W).toAffine.negY x₁' y₁') ≠ 0 :=
      mul_ne_zero (pow_ne_zero 3 hu) hden'
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

lemma addX_variableChange (x₁' x₂' ℓ : K) :
    W.addX (vcX C x₁') (vcX C x₂') ((C.u : K) * ℓ + C.s)
      = vcX C ((C • W).toAffine.addX x₁' x₂' ℓ) := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero'
  simp only [addX, vcX, variableChange_a₁, variableChange_a₂, Units.val_inv_eq_inv_val]
  field_simp
  ring

lemma addY_variableChange (x₁' x₂' y₁' ℓ : K) :
    W.addY (vcX C x₁') (vcX C x₂') (vcY C x₁' y₁') ((C.u : K) * ℓ + C.s)
      = vcY C ((C • W).toAffine.addX x₁' x₂' ℓ) ((C • W).toAffine.addY x₁' x₂' y₁' ℓ) := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero'
  simp only [addY, negAddY, addX, negY, vcX, vcY, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

private lemma some_eq_some' {V : WeierstrassCurve.Affine K} {x₁ y₁ x₂ y₂ : K}
    {h₁ : V.Nonsingular x₁ y₁} {h₂ : V.Nonsingular x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : V.Point) = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

theorem vcFun_add' [DecidableEq K] (P Q : (C • W).toAffine.Point) :
    vcFun C W (P + Q) = vcFun C W P + vcFun C W Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rfl
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
  · rw [add_of_Y_eq hxy.1 hxy.2]
    change (0 : W.Point) = Point.some (vcX C x₁) (vcY C x₁ y₁) _ + Point.some (vcX C x₂) (vcY C x₂ y₂) _
    have hxyW := (Yeq_variableChange_iff (W := W) x₁ x₂ y₁ y₂).mpr hxy
    exact (add_of_Y_eq hxyW.1 hxyW.2).symm
  · have hxyW : ¬(vcX C x₁ = vcX C x₂ ∧ vcY C x₁ y₁ = W.negY (vcX C x₂) (vcY C x₂ y₂)) :=
      fun h => hxy ((Yeq_variableChange_iff x₁ x₂ y₁ y₂).mp h)
    have hslope := slope_variableChange (W := W) x₁ x₂ y₁ y₂ h₁.1 h₂.1 hxy
    rw [add_some hxy]
    change Point.some (vcX C _) (vcY C _ _) _ =
      Point.some (vcX C x₁) (vcY C x₁ y₁) _ + Point.some (vcX C x₂) (vcY C x₂ y₂) _
    rw [add_some hxyW]
    refine some_eq_some' ?_ ?_
    · rw [hslope, addX_variableChange]
    · rw [hslope, addY_variableChange]

end VCAdd

section VC

variable {K : Type*} [Field K] [DecidableEq K] (C : VariableChange K)
  (W : WeierstrassCurve.Affine K)

theorem vcFun_injective : Function.Injective (vcFun C W) :=
  (vcFun_leftInverse (C := C) (W := W)).injective

theorem vcInvFun_add' (P Q : W.Point) :
    vcInvFun C W (P + Q) = vcInvFun C W P + vcInvFun C W Q := by
  apply vcFun_injective C W
  rw [vcFun_add', vcFun_rightInverse, vcFun_rightInverse, vcFun_rightInverse]

noncomputable def vcHom : (C • W).toAffine.Point →+ W.Point where
  toFun := vcFun C W
  map_zero' := rfl
  map_add' P Q := vcFun_add' P Q

noncomputable def vcInvHom : W.Point →+ (C • W).toAffine.Point where
  toFun := vcInvFun C W
  map_zero' := rfl
  map_add' := vcInvFun_add' C W

@[scoped simp] theorem vcHom_apply (P : (C • W).toAffine.Point) : vcHom C W P = vcFun C W P := rfl
@[scoped simp] theorem vcInvHom_apply (P : W.Point) : vcInvHom C W P = vcInvFun C W P := rfl

theorem vcHom_comp_vcInvHom : (vcHom C W).comp (vcInvHom C W) = AddMonoidHom.id _ := by
  ext P
  exact vcFun_rightInverse (C := C) (W := W) P

theorem vcInvHom_comp_vcHom : (vcInvHom C W).comp (vcHom C W) = AddMonoidHom.id _ := by
  ext P
  exact vcFun_leftInverse (C := C) (W := W) P

omit [DecidableEq K] in
theorem vcInvFun_some' {x y : K} (h : W.Nonsingular x y) :
    vcInvFun C W (.some x y h) = .some (vcXInv C x) (vcYInv C x y)
      ((nonsingular_variableChange_iff (vcXInv C x) (vcYInv C x y)).mpr
        (by rwa [vcX_vcXInv, vcY_vcYInv])) := rfl

omit [DecidableEq K] in
theorem vcFun_some' {x y : K} (h : (C • W).toAffine.Nonsingular x y) :
    vcFun C W (.some x y h) = .some (vcX C x) (vcY C x y)
      ((nonsingular_variableChange_iff x y).mp h) := rfl

theorem equivOfVariableChangeEq_rfl :
    equivOfVariableChangeEq (rfl : C • W = C • W) = variableChangeEquiv C W := rfl

theorem equivOfVariableChangeEq_rfl_symm_apply (P : W.Point) :
    (equivOfVariableChangeEq (rfl : C • W = C • W)).symm P = vcInvFun C W P := rfl

end VC

section Rational

variable {K : Type*} [Field K] [DecidableEq K]

omit [DecidableEq K] in
theorem evalEvalBC_self (p : K[X][Y]) (x y : K) :
    WeierstrassCurve.evalEvalBC K p x y = p.evalEval x y := by
  simp [WeierstrassCurve.evalEvalBC, Polynomial.map_id]

omit [DecidableEq K] in
private theorem some_congr {V : WeierstrassCurve.Affine K} {x₁ x₂ y₁ y₂ : K}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

variable (C : VariableChange K) (X : WeierstrassCurve K)

theorem isRationallyRepresented_vcInvHom :
    IsRationallyRepresented K X (C • X) (vcInvHom C X) := by
  set c : K := ((C.u⁻¹ : Kˣ) : K) with hc
  refine ⟨Polynomial.C (Polynomial.C (c ^ 2) * (Polynomial.X - Polynomial.C C.r)), 1,
    Polynomial.C (Polynomial.C (c ^ 3)) *
      (Polynomial.X - Polynomial.C (Polynomial.C C.t +
        Polynomial.C C.s * (Polynomial.X - Polynomial.C C.r))), 1,
    ∅, Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : WeierstrassCurve.evalEvalBC K (1 : K[X][Y]) x y = 1 := by
    rw [evalEvalBC_self, evalEval_one]
  have e1 : WeierstrassCurve.evalEvalBC K
      (Polynomial.C (Polynomial.C (c ^ 2) * (Polynomial.X - Polynomial.C C.r))) x y /
        WeierstrassCurve.evalEvalBC K (1 : K[X][Y]) x y = vcXInv C x := by
    rw [e0, div_one, evalEvalBC_self, evalEval_C]
    simp [vcXInv, hc]
  have e2 : WeierstrassCurve.evalEvalBC K
      (Polynomial.C (Polynomial.C (c ^ 3)) *
        (Polynomial.X - Polynomial.C (Polynomial.C C.t +
          Polynomial.C C.s * (Polynomial.X - Polynomial.C C.r)))) x y /
        WeierstrassCurve.evalEvalBC K (1 : K[X][Y]) x y = vcYInv C x y := by
    rw [e0, div_one, evalEvalBC_self]
    simp only [evalEval_mul, evalEval_C, evalEval_sub, evalEval_X, eval_C,
      eval_add, eval_mul, eval_sub, eval_X]
    simp [vcYInv, hc]
    ring
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  suffices H : ∀ a b : K, a = vcXInv C x → b = vcYInv C x y →
      ∃ h', vcInvHom C X (.some x y h) = .some a b h' from H _ _ e1 e2
  rintro a b rfl rfl
  exact ⟨_, rfl⟩

theorem isRationallyRepresented_vcHom :
    IsRationallyRepresented K (C • X) X (vcHom C X) := by
  set u : K := ((C.u : Kˣ) : K) with hu
  refine ⟨Polynomial.C (Polynomial.C (u ^ 2) * Polynomial.X + Polynomial.C C.r), 1,
    Polynomial.C (Polynomial.C (u ^ 3)) * Polynomial.X +
      Polynomial.C (Polynomial.C (u ^ 2 * C.s) * Polynomial.X + Polynomial.C C.t), 1,
    ∅, Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : WeierstrassCurve.evalEvalBC K (1 : K[X][Y]) x y = 1 := by
    rw [evalEvalBC_self, evalEval_one]
  have e1 : WeierstrassCurve.evalEvalBC K
      (Polynomial.C (Polynomial.C (u ^ 2) * Polynomial.X + Polynomial.C C.r)) x y /
        WeierstrassCurve.evalEvalBC K (1 : K[X][Y]) x y = vcX C x := by
    rw [e0, div_one, evalEvalBC_self, evalEval_C]
    simp [vcX, hu]
  have e2 : WeierstrassCurve.evalEvalBC K
      (Polynomial.C (Polynomial.C (u ^ 3)) * Polynomial.X +
        Polynomial.C (Polynomial.C (u ^ 2 * C.s) * Polynomial.X + Polynomial.C C.t)) x y /
        WeierstrassCurve.evalEvalBC K (1 : K[X][Y]) x y = vcY C x y := by
    rw [e0, div_one, evalEvalBC_self]
    simp only [evalEval_mul, evalEval_C, evalEval_X, eval_C, evalEval_add,
      eval_add, eval_mul, eval_X]
    simp [vcY, hu]
    ring
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  suffices H : ∀ a b : K, a = vcX C x → b = vcY C x y →
      ∃ h', vcHom C X (.some x y h) = .some a b h' from H _ _ e1 e2
  rintro a b rfl rfl
  exact ⟨_, rfl⟩

noncomputable def theta {X X₂ : WeierstrassCurve K} (C : VariableChange K) (h : C • X = X₂) :
    X.toAffine.Point →+ X₂.toAffine.Point :=
  (WeierstrassCurve.pointAddEquivOfEq h).toAddMonoidHom.comp (vcInvHom C X)

noncomputable def theta' {X X₂ : WeierstrassCurve K} (C : VariableChange K) (h : C • X = X₂) :
    X₂.toAffine.Point →+ X.toAffine.Point :=
  (vcHom C X).comp (WeierstrassCurve.pointAddEquivOfEq h).symm.toAddMonoidHom

variable {C X}

theorem theta_mem {X₂ : WeierstrassCurve K} (h : C • X = X₂) :
    theta C h ∈ rationalHomSet K X X₂ := by
  subst h
  refine Or.inr ?_
  have : theta C (rfl : C • X = C • X) = vcInvHom C X := by
    ext P; simp [theta]
  rw [this]
  exact isRationallyRepresented_vcInvHom C X

theorem theta'_mem {X₂ : WeierstrassCurve K} (h : C • X = X₂) :
    theta' C h ∈ rationalHomSet K X₂ X := by
  subst h
  refine Or.inr ?_
  have : theta' C (rfl : C • X = C • X) = vcHom C X := by
    ext P; simp [theta']
  rw [this]
  exact isRationallyRepresented_vcHom C X

theorem theta'_comp_theta {X₂ : WeierstrassCurve K} (h : C • X = X₂) :
    (theta' C h).comp (theta C h) = AddMonoidHom.id _ := by
  subst h
  ext P
  simp [theta, theta']
  exact vcFun_rightInverse (C := C) (W := X) P

theorem theta_comp_theta' {X₂ : WeierstrassCurve K} (h : C • X = X₂) :
    (theta C h).comp (theta' C h) = AddMonoidHom.id _ := by
  subst h
  ext P
  simp [theta, theta']
  exact vcFun_leftInverse (C := C) (W := X) P

theorem theta_zero {X₂ : WeierstrassCurve K} (h : C • X = X₂) : theta C h 0 = 0 := map_zero _

theorem theta_some {X₂ : WeierstrassCurve K} (h : C • X = X₂) {x y : K}
    (hxy : X.toAffine.Nonsingular x y) :
    ∃ h', theta C h (.some x y hxy) = .some (vcXInv C x) (vcYInv C x y) h' := by
  subst h
  exact ⟨(nonsingular_variableChange_iff (vcXInv C x) (vcYInv C x y)).mpr
    (by rwa [vcX_vcXInv, vcY_vcYInv]), by simp [theta, vcInvFun_some']⟩

end Rational

section Main

variable {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
  [DecidableEq (ResidueField A)]

omit [DecidableEq L] [DecidableEq (ResidueField A)] in

theorem exists_variableChange_map_residue_eq (v : VariableChange (ResidueField A)) :
    ∃ w : VariableChange A, w.map (residue A) = v := by
  obtain ⟨u, r, s, t⟩ := v
  obtain ⟨a, ha⟩ := residue_surjective (R := A) (u : ResidueField A)
  obtain ⟨r', hr⟩ := residue_surjective (R := A) r
  obtain ⟨s', hs⟩ := residue_surjective (R := A) s
  obtain ⟨t', ht⟩ := residue_surjective (R := A) t
  have hu : IsUnit a := (residue_ne_zero_iff_isUnit a).mp (by rw [ha]; exact u.ne_zero)
  refine ⟨⟨hu.unit, r', s', t'⟩, ?_⟩
  simp only [VariableChange.map]
  congr
  exact Units.ext (by simp [ha])

@[scoped simp] theorem reduceHom_apply {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0)
    (P : (W.map A.subtype).toAffine.Point) : reduceHom hΔ P = reducePoint hΔ P := rfl

theorem main (E' : WeierstrassCurve A) (hΔ' : (E'.map (residue A)).Δ ≠ 0)
    {V : WeierstrassCurve (ResidueField A)} (v : VariableChange (ResidueField A))
    (hv : v • E'.map (residue A) = V) :
    ∃ (E : WeierstrassCurve A) (hΔ : (E.map (residue A)).Δ ≠ 0) (hred : E.map (residue A) = V),
    ∃ θ ∈ rationalHomSet L (E'.map A.subtype) (E.map A.subtype),
    ∃ θ' ∈ rationalHomSet L (E.map A.subtype) (E'.map A.subtype),
      θ'.comp θ = AddMonoidHom.id _ ∧ θ.comp θ' = AddMonoidHom.id _ ∧
      ∀ P : (E'.map A.subtype).toAffine.Point,
        WeierstrassCurve.pointAddEquivOfEq hred (reduceHom hΔ (θ P)) =
          (equivOfVariableChangeEq hv).symm (reduceHom hΔ' P) := by
  subst hv
  obtain ⟨w, rfl⟩ := exists_variableChange_map_residue_eq v
  have hred : (w • E').map (residue A) = w.map (residue A) • E'.map (residue A) :=
    (map_variableChange E' w (residue A)).symm
  have hΔ : ((w • E').map (residue A)).Δ ≠ 0 := by
    rw [hred, variableChange_Δ]
    exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hΔ'
  have hL : (w.map A.subtype) • (E'.map A.subtype) = (w • E').map A.subtype :=
    map_variableChange E' w A.subtype
  refine ⟨w • E', hΔ, hred, theta (w.map A.subtype) hL, theta_mem hL,
    theta' (w.map A.subtype) hL, theta'_mem hL, theta'_comp_theta hL, theta_comp_theta' hL,
    fun P => ?_⟩
  rw [equivOfVariableChangeEq_rfl_symm_apply]
  rcases P with _ | ⟨x, y, hP⟩
  ·
    have h0 : theta (w.map A.subtype) hL (0 : (E'.map A.subtype).toAffine.Point) = 0 :=
      map_zero _
    change WeierstrassCurve.pointAddEquivOfEq hred (reduceHom hΔ (theta (w.map A.subtype) hL 0))
      = vcInvFun _ _ (reduceHom hΔ' 0)
    rw [h0, _root_.map_zero, _root_.map_zero, _root_.map_zero]
    rfl
  · obtain ⟨h₁, hθ⟩ := theta_some hL hP
    erw [hθ]

    have hu : (((w.map A.subtype).u⁻¹ : Lˣ) : L) = (((w.u⁻¹ : Aˣ) : A) : L) := by
      rw [VariableChange.map_u, Units.coe_map_inv]; rfl
    have hr : (w.map A.subtype).r = (w.r : L) := VariableChange.map_r _ _
    have hs : (w.map A.subtype).s = (w.s : L) := VariableChange.map_s _ _
    have ht : (w.map A.subtype).t = (w.t : L) := VariableChange.map_t _ _
    have huk : (((w.map (residue A)).u⁻¹ : (ResidueField A)ˣ) : ResidueField A)
        = residue A ((w.u⁻¹ : Aˣ) : A) := by
      rw [VariableChange.map_u, Units.coe_map_inv]; rfl
    have hrk : (w.map (residue A)).r = residue A w.r := VariableChange.map_r _ _
    have hsk : (w.map (residue A)).s = residue A w.s := VariableChange.map_s _ _
    have htk : (w.map (residue A)).t = residue A w.t := VariableChange.map_t _ _
    by_cases hx : x ∈ A
    ·
      have hy : y ∈ A := Affine.Y_mem_of_X_mem E' hP.1 hx
      set X₁A : A := ((w.u⁻¹ : Aˣ) : A) ^ 2 * (⟨x, hx⟩ - w.r) with hX₁A
      set Y₁A : A := ((w.u⁻¹ : Aˣ) : A) ^ 3 * (⟨y, hy⟩ - w.t - w.s * (⟨x, hx⟩ - w.r)) with hY₁A
      have hX₁ : vcXInv (w.map A.subtype) x = (X₁A : L) := by
        simp only [vcXInv, hu, hr, hX₁A]
        push_cast
        ring
      have hY₁ : vcYInv (w.map A.subtype) x y = (Y₁A : L) := by
        simp only [vcYInv, hu, hr, hs, ht, hY₁A]
        push_cast
        ring
      have hX₁mem : vcXInv (w.map A.subtype) x ∈ A := by rw [hX₁]; exact X₁A.2
      rw [reduceHom_apply, reducePoint_some_of_mem hΔ h₁ hX₁mem,
        WeierstrassCurve.pointAddEquivOfEq_some, reduceHom_apply,
        reducePoint_some_of_mem hΔ' hP hx, vcInvFun_some']
      refine some_congr ?_ ?_ _ _
      · rw [ValuationSubring.residue_eq_of_coe_eq (A := A) hX₁mem (v := X₁A) hX₁]
        simp only [vcXInv, huk, hrk, hX₁A, map_mul, map_pow, map_sub]
      · rw [ValuationSubring.residue_eq_of_coe_eq (A := A) _ (v := Y₁A) hY₁]
        simp only [vcYInv, huk, hrk, hsk, htk, hY₁A, map_mul, map_pow, map_sub]
    ·
      have hX₁ : vcXInv (w.map A.subtype) x ∉ A := by
        intro hmem
        apply hx
        have hx' : x = vcX (w.map A.subtype) (vcXInv (w.map A.subtype) x) :=
          (vcX_vcXInv x).symm
        rw [hx', vcX]
        refine A.toSubring.add_mem (A.toSubring.mul_mem (pow_mem ?_ 2) hmem) ?_
        · rw [VariableChange.map_u, Units.coe_map]; exact SetLike.coe_mem _
        · rw [hr]; exact SetLike.coe_mem _
      rw [reduceHom_apply, reducePoint_some_of_notMem hΔ h₁ hX₁, _root_.map_zero, reduceHom_apply,
        reducePoint_some_of_notMem hΔ' hP hx]
      rfl

end Main

end RigidificationA
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_map_residue_eq_and_reduceHom_comp_eq_of_variableChange_smul_eq.RigidificationA"

theorem solution {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
    [DecidableEq (IsLocalRing.ResidueField A)]
    (E' : WeierstrassCurve A) (hΔ' : (E'.map (IsLocalRing.residue A)).Δ ≠ 0)
    {V : WeierstrassCurve (IsLocalRing.ResidueField A)}
    (v : WeierstrassCurve.VariableChange (IsLocalRing.ResidueField A))
    (hv : v • E'.map (IsLocalRing.residue A) = V) :
    ∃ (E : WeierstrassCurve A) (hΔ : (E.map (IsLocalRing.residue A)).Δ ≠ 0)
      (hred : E.map (IsLocalRing.residue A) = V),
    ∃ θ ∈ WeierstrassCurve.rationalHomSet L (E'.map A.subtype) (E.map A.subtype),
    ∃ θ' ∈ WeierstrassCurve.rationalHomSet L (E.map A.subtype) (E'.map A.subtype),
      θ'.comp θ = AddMonoidHom.id _ ∧ θ.comp θ' = AddMonoidHom.id _ ∧
      ∀ P : (E'.map A.subtype).toAffine.Point,
        WeierstrassCurve.pointAddEquivOfEq hred (WeierstrassCurve.reduceHom hΔ (θ P)) =
          (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv).symm
            (WeierstrassCurve.reduceHom hΔ' P) :=
  RigidificationA.main E' hΔ' v hv

end S_WeierstrassCurve_exists_map_residue_eq_and_reduceHom_comp_eq_of_variableChange_smul_eq
end P2MW
export P2MW.S_WeierstrassCurve_exists_map_residue_eq_and_reduceHom_comp_eq_of_variableChange_smul_eq (solution)
