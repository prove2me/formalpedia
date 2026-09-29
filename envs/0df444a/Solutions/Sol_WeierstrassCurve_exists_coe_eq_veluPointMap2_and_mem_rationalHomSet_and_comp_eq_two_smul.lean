-- Prove2me | solution 1 for WeierstrassCurve.exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/4cd3d313-102f-52bb-ba27-33a46e05cb21

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_PointAddEquivOfEq
import Theorems.Thm_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2
import Theorems.Thm_WeierstrassCurve_exists_variableChange_eq_veluQuotient2_veluQuotient2_comp_eq_two_smul_of_two_ne_zero
import Theorems.Thm_WeierstrassCurve_veluPointMap2_surjective_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_isElliptic_veluQuotient2_of_isElliptic
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_separable
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_point_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul
p2m_attr_erase "simp" "WeierstrassCurve.vcInvEmbedding_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul.WeierstrassCurve Polynomial"
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ a₁ map a₄ a₂ Affine.Point.some Affine.nonsingular_iff' Affine.Point.some.inj toAffine Affine.Point Affine.equation_iff_nonsingular Affine.Point.some_ne_zero Δ VariableChange baseChange evalEvalBC rationalHomSet velu2XNum velu2YNum velu2X velu2Y velu2X_eq_div velu2Y_eq_div velu2_map_nonsingular veluPointMap2 veluPointMap2_some_of_ne veluQuotient2 veluGx veluGy Affine.vcYInv Affine.Point.vcInvFun Affine.Point.equivOfVariableChangeEq pointAddEquivOfEq pointAddEquivOfEq_refl exists_addMonoidHom_coe_eq_veluPointMap2 exists_variableChange_eq_veluQuotient2_veluQuotient2_comp_eq_two_smul_of_two_ne_zero veluPointMap2_surjective_of_isAlgClosed isElliptic_veluQuotient2_of_isElliptic exists_mem_rationalHomSet_comp_eq_of_ker_le_of_separable comp_mem_rationalHomSet exists_addEquiv_point_variableChange"
namespace VeluTwoIsogeny
p2m_open "WeierstrassCurve"

section VarChange

variable {K : Type*} [Field K] [DecidableEq K]

def vcAddEquiv (C : VariableChange K) (E₀ : WeierstrassCurve K) :
    E₀.toAffine.Point ≃+ (C • E₀).toAffine.Point :=
  Classical.choose (WeierstrassCurve.exists_addEquiv_point_variableChange E₀ C)

theorem vcAddEquiv_some (C : VariableChange K) (E₀ : WeierstrassCurve K) (x y : K)
    (h : E₀.toAffine.Nonsingular x y) :
    ∃ h' : (C • E₀).toAffine.Nonsingular ((↑C.u⁻¹ : K) ^ 2 * (x - C.r))
        ((↑C.u⁻¹ : K) ^ 3 * (y - C.s * x + (C.s * C.r - C.t))),
      vcAddEquiv C E₀ (.some x y h) = .some ((↑C.u⁻¹ : K) ^ 2 * (x - C.r))
        ((↑C.u⁻¹ : K) ^ 3 * (y - C.s * x + (C.s * C.r - C.t))) h' :=
  Classical.choose_spec (WeierstrassCurve.exists_addEquiv_point_variableChange E₀ C) x y h

def vS {C : VariableChange K} {E₀ V : WeierstrassCurve K} (h : C • E₀ = V) :
    E₀.toAffine.Point ≃+ V.toAffine.Point :=
  (vcAddEquiv C E₀).trans (pointAddEquivOfEq h)

private theorem some_congr {R : Type*} [CommRing R] {V : Affine R} {x₁ x₂ y₁ y₂ : R}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

theorem vS_apply {C : VariableChange K} {E₀ V : WeierstrassCurve K} (h : C • E₀ = V)
    (P : E₀.toAffine.Point) :
    vS h P = (Affine.Point.equivOfVariableChangeEq h).symm P := by
  subst h
  rcases P with _ | ⟨x, y, hP⟩
  · show vS _ 0 = _
    rw [map_zero]; rfl
  · obtain ⟨h', e⟩ := vcAddEquiv_some C E₀ x y hP
    simp only [vS, AddEquiv.trans_apply, pointAddEquivOfEq_refl, AddEquiv.refl_apply, e]
    show _ = Affine.Point.vcInvFun C E₀ (.some x y hP)
    simp only [Affine.Point.vcInvFun]
    exact some_congr rfl (by simp only [Affine.vcYInv]; ring) _ _

omit [DecidableEq K] in
private theorem exists_eq_some {W : WeierstrassCurve K}
    {P : W.toAffine.Point} {u v u' v' : K}
    {h₀ : W.toAffine.Nonsingular u v} (hP : P = .some u v h₀)
    (hu : u = u') (hv : v = v') :
    ∃ h'', P = .some u' v' h'' := by
  subst hu hv
  exact ⟨h₀, hP⟩

theorem vcAddEquiv_mem (C : VariableChange K) (E₀ : WeierstrassCurve K) :
    ((vcAddEquiv C E₀).toAddMonoidHom :
        (E₀.baseChange K).toAffine.Point →+ ((C • E₀).baseChange K).toAffine.Point) ∈
      rationalHomSet K E₀ (C • E₀) := by
  right
  refine ⟨Polynomial.C (Polynomial.C ((↑C.u⁻¹ : K) ^ 2) * (X - Polynomial.C C.r)), 1,
    Polynomial.C (Polynomial.C ((↑C.u⁻¹ : K) ^ 3)) *
      (X - Polynomial.C (Polynomial.C C.s * X) + Polynomial.C (Polynomial.C (C.s * C.r - C.t))), 1, ∅,
    Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : evalEvalBC (F := K) K (1 : K[X][Y]) x y = 1 := by simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC (F := K) K
      (Polynomial.C (Polynomial.C ((↑C.u⁻¹ : K) ^ 2) * (X - Polynomial.C C.r)) : K[X][Y]) x y =
      (↑C.u⁻¹ : K) ^ 2 * (x - C.r) := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC (F := K) K
      (Polynomial.C (Polynomial.C ((↑C.u⁻¹ : K) ^ 3)) *
        (X - Polynomial.C (Polynomial.C C.s * X) +
          Polynomial.C (Polynomial.C (C.s * C.r - C.t))) : K[X][Y]) x y =
      (↑C.u⁻¹ : K) ^ 3 * (y - C.s * x + (C.s * C.r - C.t)) := by
    simp [evalEvalBC, Polynomial.evalEval]
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  obtain ⟨h', hP⟩ := vcAddEquiv_some C E₀ x y h
  exact exists_eq_some hP (by rw [e0, e1, div_one]) (by rw [e0, e2, div_one])

theorem vcAddEquiv_symm_mem (C : VariableChange K) (E₀ : WeierstrassCurve K) :
    ((vcAddEquiv C E₀).symm.toAddMonoidHom :
        ((C • E₀).baseChange K).toAffine.Point →+ (E₀.baseChange K).toAffine.Point) ∈
      rationalHomSet K (C • E₀) E₀ := by
  right
  refine ⟨Polynomial.C (Polynomial.C ((C.u : K) ^ 2) * X + Polynomial.C C.r), 1,
    Polynomial.C (Polynomial.C ((C.u : K) ^ 3)) * X +
      Polynomial.C (Polynomial.C ((C.u : K) ^ 2 * C.s) * X + Polynomial.C C.t), 1, ∅,
    Set.finite_empty, fun x' y' h' _ => ?_⟩
  have e0 : evalEvalBC (F := K) K (1 : K[X][Y]) x' y' = 1 := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC (F := K) K
      (Polynomial.C (Polynomial.C ((C.u : K) ^ 2) * X + Polynomial.C C.r) : K[X][Y]) x' y' =
      (C.u : K) ^ 2 * x' + C.r := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC (F := K) K
      (Polynomial.C (Polynomial.C ((C.u : K) ^ 3)) * X +
        Polynomial.C (Polynomial.C ((C.u : K) ^ 2 * C.s) * X + Polynomial.C C.t) : K[X][Y]) x' y' =
      (C.u : K) ^ 3 * y' + ((C.u : K) ^ 2 * C.s * x' + C.t) := by
    simp [evalEvalBC, Polynomial.evalEval]
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  set e := vcAddEquiv C E₀
  set P := e.symm (.some x' y' h') with hPdef
  have hP0 : P ≠ 0 := by
    intro h0
    have : e P = e 0 := by rw [h0]
    rw [hPdef, AddEquiv.apply_symm_apply, _root_.map_zero] at this
    exact Affine.Point.some_ne_zero _ this
  rcases hPxy : P with _ | ⟨x, y, h⟩
  · exact absurd hPxy hP0
  · obtain ⟨h'', hexy⟩ := vcAddEquiv_some C E₀ x y h
    have key : e (.some x y h) = .some x' y' h' := by
      rw [← hPxy, hPdef, AddEquiv.apply_symm_apply]
    rw [hexy] at key
    obtain ⟨hx, hy⟩ := Affine.Point.some.inj key
    have hw : (↑C.u⁻¹ : K) = (C.u : K)⁻¹ := Units.val_inv_eq_inv_val C.u
    have hu0 : (C.u : K) ≠ 0 := C.u.ne_zero
    have hPe : e.symm.toAddMonoidHom (.some x' y' h') = .some x y h := by
      show e.symm (.some x' y' h') = .some x y h
      rw [← hPdef]; exact hPxy
    refine exists_eq_some hPe ?_ ?_
    · rw [e0, e1, div_one, ← hx, hw]
      field_simp
      ring
    · rw [e0, e2, div_one, ← hx, ← hy, hw]
      field_simp
      ring

theorem vS_mem {C : VariableChange K} {E₀ V : WeierstrassCurve K} (h : C • E₀ = V) :
    ((vS h).toAddMonoidHom : (E₀.baseChange K).toAffine.Point →+ (V.baseChange K).toAffine.Point) ∈
      rationalHomSet K E₀ V := by
  subst h
  have : (vS (rfl : C • E₀ = C • E₀)).toAddMonoidHom = (vcAddEquiv C E₀).toAddMonoidHom := by
    ext P; rfl
  rw [this]
  exact vcAddEquiv_mem C E₀

theorem vS_symm_mem {C : VariableChange K} {E₀ V : WeierstrassCurve K} (h : C • E₀ = V) :
    ((vS h).symm.toAddMonoidHom :
        (V.baseChange K).toAffine.Point →+ (E₀.baseChange K).toAffine.Point) ∈
      rationalHomSet K V E₀ := by
  subst h
  have : (vS (rfl : C • E₀ = C • E₀)).symm.toAddMonoidHom = (vcAddEquiv C E₀).symm.toAddMonoidHom := by
    ext P; rfl
  rw [this]
  exact vcAddEquiv_symm_mem C E₀

theorem conj_vS_mem {C : VariableChange K} {E₀ V : WeierstrassCurve K} (h : C • E₀ = V)
    {β : E₀.toAffine.Point →+ E₀.toAffine.Point} (hβ : β ∈ rationalHomSet K E₀ E₀) :
    ((vS h).toAddMonoidHom.comp (β.comp (vS h).symm.toAddMonoidHom) :
        V.toAffine.Point →+ V.toAffine.Point) ∈ rationalHomSet K V V :=
  WeierstrassCurve.comp_mem_rationalHomSet K V E₀ V
    (WeierstrassCurve.comp_mem_rationalHomSet K V E₀ E₀ (vS_symm_mem h) hβ) (vS_mem h)

end VarChange

section Rational

variable {K : Type*} [Field K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
  (W : WeierstrassCurve K) [W.IsElliptic] {x₀ y₀ : K} (hQ : W.toAffine.Equation x₀ y₀)
  (hgy : W.veluGy x₀ y₀ = 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)

theorem veluPointMap2_mem (π : W.toAffine.Point →+ (W.veluQuotient2 x₀ y₀).toAffine.Point)
    (hπ : ⇑π = veluPointMap2 h2 hQ hgy hΔ) :
    (π : (W.baseChange K).toAffine.Point →+ ((W.veluQuotient2 x₀ y₀).baseChange K).toAffine.Point) ∈
      rationalHomSet K W (W.veluQuotient2 x₀ y₀) := by
  right
  refine ⟨Polynomial.C (X * (X - Polynomial.C x₀) ^ 2 + Polynomial.C (W.veluGx x₀ y₀) * (X - Polynomial.C x₀)),
    Polynomial.C ((X - Polynomial.C x₀) ^ 2),
    X * Polynomial.C ((X - Polynomial.C x₀) ^ 3) -
      Polynomial.C (Polynomial.C (W.veluGx x₀ y₀)) *
        (Polynomial.C (Polynomial.C W.a₁ * (X - Polynomial.C x₀)) + X - Polynomial.C (Polynomial.C y₀)) *
          Polynomial.C (X - Polynomial.C x₀),
    Polynomial.C ((X - Polynomial.C x₀) ^ 3), {x₀}, Set.finite_singleton x₀, ?_⟩
  intro x y h hx
  have hW : W.toAffine.Nonsingular x y := h
  have hx' : x ≠ x₀ := hx
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx'
  have e1 : evalEvalBC (F := K) K (Polynomial.C ((X - Polynomial.C x₀) ^ 2) : K[X][Y]) x y =
      (x - x₀) ^ 2 := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC (F := K) K (Polynomial.C ((X - Polynomial.C x₀) ^ 3) : K[X][Y]) x y =
      (x - x₀) ^ 3 := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e3 : evalEvalBC (F := K) K
      (Polynomial.C (X * (X - Polynomial.C x₀) ^ 2 +
        Polynomial.C (W.veluGx x₀ y₀) * (X - Polynomial.C x₀)) : K[X][Y]) x y =
      W.velu2XNum x₀ y₀ x := by
    simp [evalEvalBC, Polynomial.evalEval, velu2XNum]
  have e4 : evalEvalBC (F := K) K
      (X * Polynomial.C ((X - Polynomial.C x₀) ^ 3) -
        Polynomial.C (Polynomial.C (W.veluGx x₀ y₀)) *
          (Polynomial.C (Polynomial.C W.a₁ * (X - Polynomial.C x₀)) + X -
            Polynomial.C (Polynomial.C y₀)) * Polynomial.C (X - Polynomial.C x₀) : K[X][Y]) x y =
      W.velu2YNum x₀ y₀ x y := by
    simp [evalEvalBC, Polynomial.evalEval, velu2YNum]
  refine ⟨by rw [e1]; exact pow_ne_zero _ hd, by rw [e2]; exact pow_ne_zero _ hd, ?_⟩
  have key : π (.some x y h) = .some _ _ (velu2_map_nonsingular h2 hW.1 hQ hgy hx' hΔ) := by
    rw [hπ]; exact veluPointMap2_some_of_ne h2 hQ hgy hΔ hW hx'
  have hxc : W.velu2X x₀ y₀ x = evalEvalBC (F := K) K
      (Polynomial.C (X * (X - Polynomial.C x₀) ^ 2 +
        Polynomial.C (W.veluGx x₀ y₀) * (X - Polynomial.C x₀)) : K[X][Y]) x y /
      evalEvalBC (F := K) K (Polynomial.C ((X - Polynomial.C x₀) ^ 2) : K[X][Y]) x y := by
    rw [e1, e3]; exact velu2X_eq_div W x₀ y₀ hx'
  have hyc : W.velu2Y x₀ y₀ x y = evalEvalBC (F := K) K
      (X * Polynomial.C ((X - Polynomial.C x₀) ^ 3) -
        Polynomial.C (Polynomial.C (W.veluGx x₀ y₀)) *
          (Polynomial.C (Polynomial.C W.a₁ * (X - Polynomial.C x₀)) + X -
            Polynomial.C (Polynomial.C y₀)) * Polynomial.C (X - Polynomial.C x₀) : K[X][Y]) x y /
      evalEvalBC (F := K) K (Polynomial.C ((X - Polynomial.C x₀) ^ 3) : K[X][Y]) x y := by
    rw [e2, e4]; exact velu2Y_eq_div W x₀ y₀ y hx'
  refine ⟨?_, key.trans ?_⟩
  · have h' := velu2_map_nonsingular h2 hW.1 hQ hgy hx' hΔ
    rw [hxc, hyc] at h'
    exact h'
  · exact some_congr hxc hyc _ _

end Rational

section Main

variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
  (W : WeierstrassCurve K) [W.IsElliptic] {x₀ y₀ : K} (hQ : W.toAffine.Equation x₀ y₀)
  (hgy : W.veluGy x₀ y₀ = 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)

include h2 hQ hgy in

theorem veluGx_ne_zero : W.veluGx x₀ y₀ ≠ 0 := by
  have hns : W.toAffine.Nonsingular x₀ y₀ := (Affine.equation_iff_nonsingular).mp hQ
  rw [Affine.nonsingular_iff'] at hns
  rcases hns.2 with h | h
  · intro h0; apply h
    have e : W.veluGx x₀ y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀ := rfl
    linear_combination -h0 + e
  · exfalso; apply h
    have e : W.veluGy x₀ y₀ = -(2 * y₀ + W.a₁ * x₀ + W.a₃) := rfl
    linear_combination e - hgy

theorem main :
    ∃ π : W.toAffine.Point →+ (W.veluQuotient2 x₀ y₀).toAffine.Point,
      ⇑π = veluPointMap2 h2 hQ hgy hΔ ∧
      π ∈ rationalHomSet K W (W.veluQuotient2 x₀ y₀) ∧
      (∃ π' ∈ rationalHomSet K (W.veluQuotient2 x₀ y₀) W,
          π'.comp π = 2 • AddMonoidHom.id _ ∧ π.comp π' = 2 • AddMonoidHom.id _) ∧
      ∀ (W₃ : WeierstrassCurve K) (_ : W₃.IsElliptic) (α : W.toAffine.Point →+ W₃.toAffine.Point),
        α ∈ rationalHomSet K W W₃ → (∀ T, π T = 0 → α T = 0) →
          ∃ β ∈ rationalHomSet K (W.veluQuotient2 x₀ y₀) W₃, α = β.comp π := by
  haveI hW' : (W.veluQuotient2 x₀ y₀).IsElliptic := isElliptic_veluQuotient2_of_isElliptic hQ hgy
  obtain ⟨π, hπ⟩ := WeierstrassCurve.exists_addMonoidHom_coe_eq_veluPointMap2 W h2 hQ hgy hΔ
  have hπmem := veluPointMap2_mem h2 W hQ hgy hΔ π hπ
  have ht₀ : W.veluGx x₀ y₀ ≠ 0 := veluGx_ne_zero h2 W hQ hgy
  refine ⟨π, hπ, hπmem, ?_, ?_⟩
  ·

    obtain ⟨x₁, y₁, hQ₁, hgy₁, hΔ₁, C, hC, hothers, hdouble⟩ :=
      WeierstrassCurve.exists_variableChange_eq_veluQuotient2_veluQuotient2_comp_eq_two_smul_of_two_ne_zero
        h2 W hQ hgy hΔ
    obtain ⟨π₁, hπ₁⟩ :=
      WeierstrassCurve.exists_addMonoidHom_coe_eq_veluPointMap2 (W.veluQuotient2 x₀ y₀) h2 hQ₁ hgy₁ hΔ₁
    have hπ₁mem := veluPointMap2_mem h2 (W.veluQuotient2 x₀ y₀) hQ₁ hgy₁ hΔ₁ π₁ hπ₁
    set π' : (W.veluQuotient2 x₀ y₀).toAffine.Point →+ W.toAffine.Point :=
      (vS hC).symm.toAddMonoidHom.comp π₁ with hπ'def
    have hπ'mem : π' ∈ rationalHomSet K (W.veluQuotient2 x₀ y₀) W :=
      WeierstrassCurve.comp_mem_rationalHomSet K (W.veluQuotient2 x₀ y₀)
        ((W.veluQuotient2 x₀ y₀).veluQuotient2 x₁ y₁) W hπ₁mem (vS_symm_mem hC)
    have hπ'π : ∀ P, π' (π P) = (2 : ℤ) • P := fun P => by
      have hd := hdouble P
      rw [← hπ, ← hπ₁] at hd
      show (vS hC).symm (π₁ (π P)) = (2 : ℤ) • P
      apply (vS hC).injective
      rw [AddEquiv.apply_symm_apply, vS_apply, ← hd, Equiv.symm_apply_apply]
    refine ⟨π', hπ'mem, ?_, ?_⟩
    · ext P
      show π' (π P) = (2 • AddMonoidHom.id _) P
      rw [hπ'π]
      simp [two_nsmul, two_zsmul]
    ·
      have hsurj : Function.Surjective π := by
        rw [hπ]; exact veluPointMap2_surjective_of_isAlgClosed W h2 hQ hgy hΔ
      ext Q
      obtain ⟨P, rfl⟩ := hsurj Q
      show π (π' (π P)) = (2 • AddMonoidHom.id _) (π P)
      rw [hπ'π, map_zsmul]
      show (2 : ℤ) • π P = 2 • π P
      simp [two_zsmul, two_nsmul]
  ·

    intro W₃ _ α hα hker

    let Pn : K[X] := Polynomial.C 1 * X ^ 2 + Polynomial.C (-x₀) * X + Polynomial.C (W.veluGx x₀ y₀)
    let S : K[X] := X - Polynomial.C x₀
    let N₀ : K[X] := Polynomial.C (-(W.veluGx x₀ y₀ * W.a₁)) * (X - Polynomial.C x₀) +
      Polynomial.C (W.veluGx x₀ y₀ * y₀)
    let N₁ : K[X] := (X - Polynomial.C x₀) ^ 2 - Polynomial.C (W.veluGx x₀ y₀)
    let R : K[X] := (X - Polynomial.C x₀) ^ 2
    have hmonic : Pn.Monic := by
      show Polynomial.leadingCoeff Pn = 1
      exact Polynomial.leadingCoeff_quadratic one_ne_zero
    have hdeg : Pn.natDegree = S.natDegree + 1 := by
      show (Polynomial.C 1 * X ^ 2 + Polynomial.C (-x₀) * X + Polynomial.C (W.veluGx x₀ y₀)).natDegree =
        (X - Polynomial.C x₀).natDegree + 1
      rw [Polynomial.natDegree_quadratic one_ne_zero, Polynomial.natDegree_X_sub_C]
    have hcop : IsCoprime Pn S := by
      refine ⟨Polynomial.C (W.veluGx x₀ y₀)⁻¹, -(Polynomial.C (W.veluGx x₀ y₀)⁻¹ * X), ?_⟩
      have ht : (W.veluGx x₀ y₀)⁻¹ * W.veluGx x₀ y₀ = 1 := inv_mul_cancel₀ ht₀
      calc Polynomial.C (W.veluGx x₀ y₀)⁻¹ * Pn + -(Polynomial.C (W.veluGx x₀ y₀)⁻¹ * X) * S
          = Polynomial.C (W.veluGx x₀ y₀)⁻¹ * (Pn - X * S) := by ring
        _ = Polynomial.C (W.veluGx x₀ y₀)⁻¹ * Polynomial.C (W.veluGx x₀ y₀) := by
          congr 1
          show Polynomial.C 1 * X ^ 2 + Polynomial.C (-x₀) * X + Polynomial.C (W.veluGx x₀ y₀) -
            X * (X - Polynomial.C x₀) = Polynomial.C (W.veluGx x₀ y₀)
          simp only [map_one, map_neg, one_mul]
          ring
        _ = 1 := by rw [← Polynomial.C_mul, ht, Polynomial.C_1]
    have hφ : ∀ (x y : K) (h : (W.baseChange K).toAffine.Nonsingular x y), x ∉ ({x₀} : Set K) →
        aeval x S ≠ 0 ∧ aeval x R ≠ 0 ∧
        ∃ h', π (.some x y h) =
          .some (aeval x Pn / aeval x S) ((aeval x N₀ + aeval x N₁ * y) / aeval x R) h' := by
      intro x y h hx
      have hW : W.toAffine.Nonsingular x y := h
      have hx' : x ≠ x₀ := hx
      have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx'
      have eS : aeval x S = x - x₀ := by simp [S]
      have eR : aeval x R = (x - x₀) ^ 2 := by simp [R]
      have eP : aeval x Pn = x ^ 2 - x₀ * x + W.veluGx x₀ y₀ := by simp [Pn]; ring
      have eN₀ : aeval x N₀ = -(W.veluGx x₀ y₀ * W.a₁) * (x - x₀) + W.veluGx x₀ y₀ * y₀ := by
        simp [N₀]
      have eN₁ : aeval x N₁ = (x - x₀) ^ 2 - W.veluGx x₀ y₀ := by simp [N₁]
      refine ⟨by rw [eS]; exact hd, by rw [eR]; exact pow_ne_zero _ hd, ?_⟩
      have key : π (.some x y h) = .some _ _ (velu2_map_nonsingular h2 hW.1 hQ hgy hx' hΔ) := by
        rw [hπ]; exact veluPointMap2_some_of_ne h2 hQ hgy hΔ hW hx'
      have hxc : W.velu2X x₀ y₀ x = aeval x Pn / aeval x S := by
        rw [eP, eS, velu2X]
        field_simp
      have hyc : W.velu2Y x₀ y₀ x y = (aeval x N₀ + aeval x N₁ * y) / aeval x R := by
        rw [eN₀, eN₁, eR, velu2Y]
        field_simp
        ring
      refine ⟨?_, key.trans ?_⟩
      · have h' := velu2_map_nonsingular h2 hW.1 hQ hgy hx' hΔ
        rw [hxc, hyc] at h'
        exact h'
      · exact some_congr hxc hyc _ _
    obtain ⟨β, hβ, hfac⟩ :=
      WeierstrassCurve.exists_mem_rationalHomSet_comp_eq_of_ker_le_of_separable K W
        (W.veluQuotient2 x₀ y₀) W₃ hα hmonic hdeg hcop (Set.finite_singleton x₀) hφ hker
    exact ⟨β, hβ, by ext T; exact hfac T⟩

end Main

end WeierstrassCurve.VeluTwoIsogeny

end

theorem solution {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (h2 : (2 : K) ≠ 0) (W : WeierstrassCurve K) [W.IsElliptic] {x₀ y₀ : K} (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) : ∃ π : W.toAffine.Point →+ (W.veluQuotient2 x₀ y₀).toAffine.Point, ⇑π = WeierstrassCurve.veluPointMap2 h2 hQ hgy hΔ ∧ π ∈ WeierstrassCurve.rationalHomSet K W (W.veluQuotient2 x₀ y₀) ∧ (∃ π' ∈ WeierstrassCurve.rationalHomSet K (W.veluQuotient2 x₀ y₀) W, π'.comp π = 2 • AddMonoidHom.id _ ∧ π.comp π' = 2 • AddMonoidHom.id _) ∧ ∀ (W₃ : WeierstrassCurve K) (_ : W₃.IsElliptic) (α : W.toAffine.Point →+ W₃.toAffine.Point), α ∈ WeierstrassCurve.rationalHomSet K W W₃ → (∀ T, π T = 0 → α T = 0) → ∃ β ∈ WeierstrassCurve.rationalHomSet K (W.veluQuotient2 x₀ y₀) W₃, α = β.comp π :=
  WeierstrassCurve.VeluTwoIsogeny.main h2 W hQ hgy hΔ

end S_WeierstrassCurve_exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul
end P2MW
export P2MW.S_WeierstrassCurve_exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul (solution)
