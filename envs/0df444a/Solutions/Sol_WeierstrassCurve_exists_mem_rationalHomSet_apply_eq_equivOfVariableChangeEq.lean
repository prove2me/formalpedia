-- Prove2me | solution 1 for WeierstrassCurve.exists_mem_rationalHomSet_apply_eq_equivOfVariableChangeEq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/0e05966e-ca07-5f21-a2c2-2b1a02a075a4

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_apply_eq_equivOfVariableChangeEq

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine toAffine Affine.Point VariableChange evalEvalBC IsRationallyRepresented rationalHomSet Affine.Point.equivOfVariableChangeEq Affine.Point.vcInvFun_add"
namespace VCIsoRational
p2m_open "WeierstrassCurve"

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_apply_eq_equivOfVariableChangeEq.WeierstrassCurve WeierstrassCurve.Affine"

variable {k : Type*} [Field k] [DecidableEq k]

noncomputable def vcAddEquiv (γ : VariableChange k) (W : WeierstrassCurve k) :
    W.toAffine.Point ≃+ (γ • W).toAffine.Point :=
  AddEquiv.mk' (Point.variableChangeEquiv γ W.toAffine).symm
    (fun P Q => Point.vcInvFun_add γ W.toAffine P Q)

theorem vcAddEquiv_apply (γ : VariableChange k) (W : WeierstrassCurve k) (P : W.toAffine.Point) :
    vcAddEquiv γ W P = Point.vcInvFun γ W.toAffine P := rfl

theorem vcAddEquiv_symm_apply (γ : VariableChange k) (W : WeierstrassCurve k)
    (P : (γ • W).toAffine.Point) :
    (vcAddEquiv γ W).symm P = Point.vcFun γ W.toAffine P := rfl

noncomputable def vcHom (γ : VariableChange k) (W : WeierstrassCurve k) :
    (γ • W).toAffine.Point →+ W.toAffine.Point :=
  (vcAddEquiv γ W).symm.toAddMonoidHom

noncomputable def vcInvHom (γ : VariableChange k) (W : WeierstrassCurve k) :
    W.toAffine.Point →+ (γ • W).toAffine.Point :=
  (vcAddEquiv γ W).toAddMonoidHom

theorem vcHom_some (γ : VariableChange k) (W : WeierstrassCurve k) {x y : k}
    (h : (γ • W).toAffine.Nonsingular x y) :
    vcHom γ W (.some x y h) =
      .some (vcX γ x) (vcY γ x y) ((nonsingular_variableChange_iff x y).mp h) := rfl

theorem vcInvHom_some (γ : VariableChange k) (W : WeierstrassCurve k) {x y : k}
    (h : W.toAffine.Nonsingular x y) :
    vcInvHom γ W (.some x y h) =
      .some (vcXInv γ x) (vcYInv γ x y)
        ((nonsingular_variableChange_iff (vcXInv γ x) (vcYInv γ x y)).mpr
          (by rwa [vcX_vcXInv, vcY_vcYInv])) := rfl

theorem vcInvHom_comp_vcHom (γ : VariableChange k) (W : WeierstrassCurve k) :
    (vcInvHom γ W).comp (vcHom γ W) = AddMonoidHom.id _ :=
  AddMonoidHom.ext fun P => (vcAddEquiv γ W).apply_symm_apply P

theorem vcHom_comp_vcInvHom (γ : VariableChange k) (W : WeierstrassCurve k) :
    (vcHom γ W).comp (vcInvHom γ W) = AddMonoidHom.id _ :=
  AddMonoidHom.ext fun P => (vcAddEquiv γ W).symm_apply_apply P

theorem vcHom_apply_eq_equivOfVariableChangeEq (γ : VariableChange k) (W : WeierstrassCurve k)
    (P : (γ • W).toAffine.Point) :
    vcHom γ W P = Point.equivOfVariableChangeEq (C := γ) (W := W.toAffine) rfl P := rfl

theorem some_eq_some {W' : WeierstrassCurve.Affine k} {x₁ y₁ x₂ y₂ : k}
    (hx : x₁ = x₂) (hy : y₁ = y₂) {h₁ : W'.Nonsingular x₁ y₁} {h₂ : W'.Nonsingular x₂ y₂} :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx hy; rfl

theorem evalEvalBC_one (x y : k) : evalEvalBC k (1 : k[X][Y]) x y = 1 := by
  simp [evalEvalBC]

noncomputable def nX (γ : VariableChange k) : k[X][Y] :=
  Polynomial.C (Polynomial.C ((γ.u : k) ^ 2) * Polynomial.X + Polynomial.C γ.r)

noncomputable def nY (γ : VariableChange k) : k[X][Y] :=
  Polynomial.C (Polynomial.C ((γ.u : k) ^ 3)) * Y +
    Polynomial.C (Polynomial.C ((γ.u : k) ^ 2 * γ.s) * Polynomial.X + Polynomial.C γ.t)

noncomputable def nXInv (γ : VariableChange k) : k[X][Y] :=
  Polynomial.C (Polynomial.C (((γ.u⁻¹ : kˣ) : k) ^ 2) * (Polynomial.X - Polynomial.C γ.r))

noncomputable def nYInv (γ : VariableChange k) : k[X][Y] :=
  Polynomial.C (Polynomial.C (((γ.u⁻¹ : kˣ) : k) ^ 3)) *
    (Y - Polynomial.C (Polynomial.C γ.t) -
      Polynomial.C (Polynomial.C γ.s * (Polynomial.X - Polynomial.C γ.r)))

theorem evalEvalBC_nX (γ : VariableChange k) (x y : k) :
    evalEvalBC k (nX γ) x y = vcX γ x := by
  simp [evalEvalBC, nX, vcX, Polynomial.evalEval_C]

theorem evalEvalBC_nY (γ : VariableChange k) (x y : k) :
    evalEvalBC k (nY γ) x y = vcY γ x y := by
  simp [evalEvalBC, nY, vcY, Polynomial.evalEval_C, add_assoc]

theorem evalEvalBC_nXInv (γ : VariableChange k) (x y : k) :
    evalEvalBC k (nXInv γ) x y = vcXInv γ x := by
  simp [evalEvalBC, nXInv, vcXInv, Polynomial.evalEval_C]

theorem evalEvalBC_nYInv (γ : VariableChange k) (x y : k) :
    evalEvalBC k (nYInv γ) x y = vcYInv γ x y := by
  simp [evalEvalBC, nYInv, vcYInv, Polynomial.evalEval_C]

theorem isRationallyRepresented_vcHom (γ : VariableChange k) (W : WeierstrassCurve k) :
    IsRationallyRepresented k (γ • W) W (vcHom γ W) := by
  refine ⟨nX γ, 1, nY γ, 1, ∅, Set.finite_empty, fun x y h _ => ?_⟩
  have e1 := evalEvalBC_one (k := k) x y
  have eX : evalEvalBC k (nX γ) x y / evalEvalBC k (1 : k[X][Y]) x y = vcX γ x := by
    rw [e1, div_one, evalEvalBC_nX]
  have eY : evalEvalBC k (nY γ) x y / evalEvalBC k (1 : k[X][Y]) x y = vcY γ x y := by
    rw [e1, div_one, evalEvalBC_nY]
  refine ⟨by rw [e1]; exact one_ne_zero, by rw [e1]; exact one_ne_zero, ?_⟩
  suffices H : ∀ a b : k, a = vcX γ x → b = vcY γ x y →
      ∃ h', vcHom γ W (.some x y h) = .some a b h' from H _ _ eX eY
  rintro a b rfl rfl
  exact ⟨_, vcHom_some γ W h⟩

theorem isRationallyRepresented_vcInvHom (γ : VariableChange k) (W : WeierstrassCurve k) :
    IsRationallyRepresented k W (γ • W) (vcInvHom γ W) := by
  refine ⟨nXInv γ, 1, nYInv γ, 1, ∅, Set.finite_empty, fun x y h _ => ?_⟩
  have e1 := evalEvalBC_one (k := k) x y
  have eX : evalEvalBC k (nXInv γ) x y / evalEvalBC k (1 : k[X][Y]) x y = vcXInv γ x := by
    rw [e1, div_one, evalEvalBC_nXInv]
  have eY : evalEvalBC k (nYInv γ) x y / evalEvalBC k (1 : k[X][Y]) x y = vcYInv γ x y := by
    rw [e1, div_one, evalEvalBC_nYInv]
  refine ⟨by rw [e1]; exact one_ne_zero, by rw [e1]; exact one_ne_zero, ?_⟩
  suffices H : ∀ a b : k, a = vcXInv γ x → b = vcYInv γ x y →
      ∃ h', vcInvHom γ W (.some x y h) = .some a b h' from H _ _ eX eY
  rintro a b rfl rfl
  exact ⟨_, vcInvHom_some γ W h⟩

theorem vcHom_mem_rationalHomSet (γ : VariableChange k) (W : WeierstrassCurve k) :
    vcHom γ W ∈ rationalHomSet k (γ • W) W :=
  Or.inr (isRationallyRepresented_vcHom γ W)

theorem vcInvHom_mem_rationalHomSet (γ : VariableChange k) (W : WeierstrassCurve k) :
    vcInvHom γ W ∈ rationalHomSet k W (γ • W) :=
  Or.inr (isRationallyRepresented_vcInvHom γ W)

theorem main (W : WeierstrassCurve k) (γ : VariableChange k) {V : WeierstrassCurve k}
    (h : γ • W = V) :
    ∃ ι ∈ rationalHomSet k V W, ∃ ι' ∈ rationalHomSet k W V,
      (∀ P : V.toAffine.Point, ι P = Point.equivOfVariableChangeEq h P) ∧
        ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _ := by
  subst h
  exact ⟨vcHom γ W, vcHom_mem_rationalHomSet γ W, vcInvHom γ W, vcInvHom_mem_rationalHomSet γ W,
    vcHom_apply_eq_equivOfVariableChangeEq γ W, vcInvHom_comp_vcHom γ W, vcHom_comp_vcInvHom γ W⟩

end WeierstrassCurve.VCIsoRational

theorem solution
    {k : Type*} [Field k] [DecidableEq k] (W : WeierstrassCurve k) (γ : WeierstrassCurve.VariableChange k)
    {V : WeierstrassCurve k} (h : γ • W = V) :
    ∃ ι ∈ WeierstrassCurve.rationalHomSet k V W, ∃ ι' ∈ WeierstrassCurve.rationalHomSet k W V,
      (∀ P : V.toAffine.Point, ι P = WeierstrassCurve.Affine.Point.equivOfVariableChangeEq h P) ∧
        ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _ :=
  WeierstrassCurve.VCIsoRational.main W γ h

end S_WeierstrassCurve_exists_mem_rationalHomSet_apply_eq_equivOfVariableChangeEq
end P2MW
export P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_apply_eq_equivOfVariableChangeEq (solution)
