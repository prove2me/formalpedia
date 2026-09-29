-- Prove2me | solution 1 for WeierstrassCurve.exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/71e771b5-6005-53c1-aa2c-a0cc6939cb70

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq

set_option autoImplicit false

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₁ map variableChange_a₃ a₄ a₂ variableChange_a₂ map_id toAffine Affine.Point variableChange_a₁ variableChange_a₄ VariableChange evalEvalBC IsRationallyRepresented rationalHomSet rationalEndSubring Affine.Point.equivOfVariableChangeEq"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "negY Y_eq_of_Y_ne slope_of_X_ne slope map Point.some Nonsingular negAddY slope_of_Y_ne Point addX addY Point.zero vcX vcY vcXInv vcYInv vcX_vcXInv vcY_vcYInv nonsingular_variableChange_iff Point.equivOfVariableChangeEq"
namespace Point
p2m_export "WeierstrassCurve.Affine.Point" "add add_of_Y_eq map_id some add_some map zero vcFun vcInvFun vcFun_zero variableChangeEquiv equivOfVariableChangeEq"
p2m_open "WeierstrassCurve.Affine.Point WeierstrassCurve.Affine WeierstrassCurve"

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve.Affine"

variable {K : Type*} [Field K] [DecidableEq K] {C : VariableChange K} {W : WeierstrassCurve.Affine K}

private lemma hu0 : (C.u : K) ≠ 0 := C.u.ne_zero

theorem vcY_negY (x y : K) : vcY C x ((C • W).toAffine.negY x y) = W.negY (vcX C x) (vcY C x y) := by
  have hu : (C.u : K) ≠ 0 := hu0
  simp only [negY, vcX, vcY, variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

theorem vcX_injective : Function.Injective (vcX C : K → K) := by
  intro a b h
  simp only [vcX] at h
  have hu : (C.u : K) ^ 2 ≠ 0 := pow_ne_zero _ hu0
  exact mul_left_cancel₀ hu (add_right_cancel h)

theorem vcY_injective (x : K) : Function.Injective (vcY C x : K → K) := by
  intro a b h
  simp only [vcY] at h
  have hu : (C.u : K) ^ 3 ≠ 0 := pow_ne_zero _ hu0
  exact mul_left_cancel₀ hu (add_right_cancel (add_right_cancel h))

theorem vc_cond_iff (x₁ x₂ y₁ y₂ : K) :
    (vcX C x₁ = vcX C x₂ ∧ vcY C x₁ y₁ = W.negY (vcX C x₂) (vcY C x₂ y₂)) ↔
      (x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂) := by
  constructor
  · rintro ⟨hx, hy⟩
    have hx' : x₁ = x₂ := vcX_injective hx
    subst hx'
    rw [← vcY_negY] at hy
    exact ⟨rfl, vcY_injective x₁ hy⟩
  · rintro ⟨rfl, hy⟩
    exact ⟨rfl, by rw [hy, vcY_negY]⟩

theorem slope_vc {x₁ x₂ y₁ y₂ : K} (h₁ : (C • W).toAffine.Nonsingular x₁ y₁) (h₂ : (C • W).toAffine.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    W.slope (vcX C x₁) (vcX C x₂) (vcY C x₁ y₁) (vcY C x₂ y₂) =
      (C.u : K) * (C • W).toAffine.slope x₁ x₂ y₁ y₂ + C.s := by
  have hu : (C.u : K) ≠ 0 := hu0
  by_cases hx : x₁ = x₂
  · subst hx
    have hy : y₁ ≠ (C • W).toAffine.negY x₁ y₂ := fun h => hxy ⟨rfl, h⟩

    have hy12 : y₁ = y₂ := by
      rcases Y_eq_of_Y_ne h₁.1 h₂.1 rfl hy with h
      exact h
    subst hy12
    have hyW : vcY C x₁ y₁ ≠ W.negY (vcX C x₁) (vcY C x₁ y₁) := by
      rw [← vcY_negY]; exact fun h => hy (vcY_injective x₁ h)
    rw [slope_of_Y_ne rfl hyW, slope_of_Y_ne rfl hy]

    have hD : vcY C x₁ y₁ - W.negY (vcX C x₁) (vcY C x₁ y₁) =
        (C.u : K) ^ 3 * (y₁ - (C • W).toAffine.negY x₁ y₁) := by
      simp only [negY, vcX, vcY, variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
      field_simp; ring
    have hN : 3 * vcX C x₁ ^ 2 + 2 * W.a₂ * vcX C x₁ + W.a₄ - W.a₁ * vcY C x₁ y₁ =
        (C.u : K) ^ 4 * (3 * x₁ ^ 2 + 2 * (C • W).toAffine.a₂ * x₁ + (C • W).toAffine.a₄ - (C • W).toAffine.a₁ * y₁) +
          C.s * ((C.u : K) ^ 3 * (y₁ - (C • W).toAffine.negY x₁ y₁)) := by
      simp only [negY, vcX, vcY, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
        Units.val_inv_eq_inv_val]
      field_simp; ring
    have hden : y₁ - (C • W).toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy
    rw [hD, hN]
    have hu3 : (C.u : K) ^ 3 * (y₁ - (C • W).toAffine.negY x₁ y₁) ≠ 0 := mul_ne_zero (pow_ne_zero _ hu) hden
    rw [div_eq_iff hu3, mul_div_assoc']
    rw [div_add' _ _ _ hden, div_mul_eq_mul_div, eq_div_iff hden]
    ring
  · have hxW : vcX C x₁ ≠ vcX C x₂ := fun h => hx (vcX_injective h)
    rw [slope_of_X_ne hxW, slope_of_X_ne hx]
    have hden : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have hdenW : vcX C x₁ - vcX C x₂ ≠ 0 := sub_ne_zero.mpr hxW
    rw [div_eq_iff hdenW, mul_div_assoc']
    rw [div_add' _ _ _ hden, div_mul_eq_mul_div, eq_div_iff hden]
    simp only [vcX, vcY]
    ring

theorem vcX_addX (x₁ x₂ L : K) :
    vcX C ((C • W).toAffine.addX x₁ x₂ L) = W.addX (vcX C x₁) (vcX C x₂) ((C.u : K) * L + C.s) := by
  have hu : (C.u : K) ≠ 0 := hu0
  simp only [addX, vcX, variableChange_a₁, variableChange_a₂, Units.val_inv_eq_inv_val]
  field_simp; ring

theorem vcY_addY (x₁ x₂ y₁ L : K) :
    vcY C ((C • W).toAffine.addX x₁ x₂ L) ((C • W).toAffine.addY x₁ x₂ y₁ L) =
      W.addY (vcX C x₁) (vcX C x₂) (vcY C x₁ y₁) ((C.u : K) * L + C.s) := by
  have hu : (C.u : K) ≠ 0 := hu0
  simp only [addY, negAddY, addX, negY, vcX, vcY, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field_simp; ring

private lemma some_eq_some' {W' : WeierstrassCurve.Affine K} {x₁ y₁ x₂ y₂ : K} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W'.Nonsingular x₁ y₁} {h₂ : W'.Nonsingular x₂ y₂} : Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx hy; rfl

variable (C W) in

theorem vcFun_add (P Q : (C • W).toAffine.Point) : vcFun C W (P + Q) = vcFun C W P + vcFun C W Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rw [show (Point.zero : (C • W).toAffine.Point) = 0 from rfl, zero_add, vcFun_zero, zero_add]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rw [show (Point.zero : (C • W).toAffine.Point) = 0 from rfl, add_zero, vcFun_zero, add_zero]
  by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
  · rw [add_of_Y_eq hxy.1 hxy.2, vcFun_zero]
    have h' := (vc_cond_iff (C := C) (W := W) x₁ x₂ y₁ y₂).mpr hxy
    show 0 = Point.some _ _ _ + Point.some _ _ _
    rw [add_of_Y_eq h'.1 h'.2]
  · have hxyW : ¬(vcX C x₁ = vcX C x₂ ∧ vcY C x₁ y₁ = W.negY (vcX C x₂) (vcY C x₂ y₂)) := by
      rw [vc_cond_iff]; exact hxy
    rw [add_some hxy]
    show Point.some _ _ _ = Point.some _ _ _ + Point.some _ _ _
    rw [add_some hxyW]
    exact some_eq_some' (by rw [vcX_addX, slope_vc h₁ h₂ hxy]) (by rw [vcY_addY, slope_vc h₁ h₂ hxy])

variable (C W) in

noncomputable def variableChangeAddEquiv : (C • W).toAffine.Point ≃+ W.Point :=
  { variableChangeEquiv C W with map_add' := vcFun_add C W }

@[scoped simp] theorem variableChangeAddEquiv_apply (P : (C • W).toAffine.Point) : variableChangeAddEquiv C W P = vcFun C W P := rfl

@[scoped simp] theorem variableChangeAddEquiv_symm_apply (P : W.Point) : (variableChangeAddEquiv C W).symm P = vcInvFun C W P := rfl

end WeierstrassCurve.Affine.Point
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve.Affine.Point"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₁ map variableChange_a₃ a₄ a₂ variableChange_a₂ map_id toAffine Affine.Point variableChange_a₁ variableChange_a₄ VariableChange evalEvalBC IsRationallyRepresented rationalHomSet rationalEndSubring Affine.Point.equivOfVariableChangeEq"
namespace VCTransport
p2m_open "WeierstrassCurve"

p2m_open "Polynomial WeierstrassCurve P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve.Affine WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve.Affine.Point"
open scoped Polynomial.Bivariate

variable {k : Type*} [Field k]

noncomputable def subst (α β γ δ ε : k) (p : k[X][Y]) : k[X][Y] :=
  (p.map (compRingHom (C α * X + C β))).comp (C (C γ) * X + C (C δ * X + C ε))

theorem evalEval_subst (α β γ δ ε : k) (p : k[X][Y]) (x y : k) :
    (subst α β γ δ ε p).evalEval x y = p.evalEval (α * x + β) (γ * y + δ * x + ε) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [subst] at hp hq ⊢; rw [Polynomial.map_add, add_comp, evalEval_add, hp, hq, evalEval_add]
  | monomial n a =>
    simp only [subst]
    rw [Polynomial.map_monomial, coe_compRingHom, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial, mul_comp, C_comp,
      pow_comp, X_comp]
    simp only [evalEval, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_comp]
    ring

theorem evalEvalBC_self (p : k[X][Y]) (x y : k) : evalEvalBC k p x y = p.evalEval x y := by
  have h1 : mapRingHom (algebraMap k k) = RingHom.id (k[X]) := by
    rw [show algebraMap k k = RingHom.id k from rfl, mapRingHom_id]
  rw [evalEvalBC, h1, Polynomial.map_id]

theorem evalEvalBC_subst (α β γ δ ε : k) (p : k[X][Y]) (x y : k) :
    evalEvalBC k (subst α β γ δ ε p) x y = evalEvalBC k p (α * x + β) (γ * y + δ * x + ε) := by
  rw [evalEvalBC_self, evalEvalBC_self, evalEval_subst]

theorem evalEvalBC_add' (p q : k[X][Y]) (x y : k) : evalEvalBC k (p + q) x y = evalEvalBC k p x y + evalEvalBC k q x y := by
  simp only [evalEvalBC_self, evalEval_add]

theorem evalEvalBC_mul' (p q : k[X][Y]) (x y : k) : evalEvalBC k (p * q) x y = evalEvalBC k p x y * evalEvalBC k q x y := by
  simp only [evalEvalBC_self, evalEval_mul]

theorem evalEvalBC_CC (c : k) (x y : k) : evalEvalBC k (C (C c) : k[X][Y]) x y = c := by
  simp only [evalEvalBC_self, evalEval_C, eval_C]

variable [DecidableEq k]

omit [DecidableEq k] in
private lemma some_eq_some' {W' : WeierstrassCurve.Affine k} {x₁ y₁ x₂ y₂ : k} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W'.Nonsingular x₁ y₁} {h₂ : W'.Nonsingular x₂ y₂} : Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx hy; rfl

theorem isRationallyRepresented_conj {W₁ W₂ : WeierstrassCurve k}
    {a : (W₁⁄k).Point →+ (W₁⁄k).Point} (ha : IsRationallyRepresented k W₁ W₁ a)
    (e : (W₂⁄k).Point → (W₁⁄k).Point) (e' : (W₁⁄k).Point → (W₂⁄k).Point)
    (α β γ δ ε α' β' γ' δ' ε' : k) (hα : α ≠ 0)
    (he : ∀ (x y : k) (h : (W₂⁄k).Nonsingular x y), ∃ h', e (.some x y h) = .some (α * x + β) (γ * y + δ * x + ε) h')
    (he' : ∀ (x y : k) (h : (W₁⁄k).Nonsingular x y), ∃ h', e' (.some x y h) = .some (α' * x + β') (γ' * y + δ' * x + ε') h')
    {b : (W₂⁄k).Point →+ (W₂⁄k).Point} (hb : ∀ P, b P = e' (a (e P))) :
    IsRationallyRepresented k W₂ W₂ b := by
  obtain ⟨nX, dX, nY, dY, B, hBfin, hrep⟩ := ha
  refine ⟨C (C α') * subst α β γ δ ε nX + C (C β') * subst α β γ δ ε dX, subst α β γ δ ε dX,
    C (C γ') * (subst α β γ δ ε nY * subst α β γ δ ε dX) + C (C δ') * (subst α β γ δ ε nX * subst α β γ δ ε dY) +
      C (C ε') * (subst α β γ δ ε dX * subst α β γ δ ε dY),
    subst α β γ δ ε dX * subst α β γ δ ε dY,
    (fun x => α * x + β) ⁻¹' B, ?_, ?_⟩
  · exact hBfin.preimage fun _ _ _ _ h => mul_left_cancel₀ hα (add_right_cancel h)
  intro x y h hx
  rw [Set.mem_preimage] at hx
  obtain ⟨h₁, he₁⟩ := he x y h
  obtain ⟨hdX, hdY, h₂, ha₂⟩ := hrep (α * x + β) (γ * y + δ * x + ε) h₁ hx
  obtain ⟨h₃, he₃⟩ := he' _ _ h₂
  simp only [evalEvalBC_add', evalEvalBC_mul', evalEvalBC_CC, evalEvalBC_subst]

  set A := evalEvalBC k nX (α * x + β) (γ * y + δ * x + ε) with hA
  set Bx := evalEvalBC k dX (α * x + β) (γ * y + δ * x + ε) with hBx
  set A₂ := evalEvalBC k nY (α * x + β) (γ * y + δ * x + ε) with hA₂
  set B₂ := evalEvalBC k dY (α * x + β) (γ * y + δ * x + ε) with hB₂
  have key : b (.some x y h) = .some (α' * (A / Bx) + β') (γ' * (A₂ / B₂) + δ' * (A / Bx) + ε') h₃ := by
    rw [hb, he₁, ha₂, he₃]
  have hX : α' * (A / Bx) + β' = (α' * A + β' * Bx) / Bx := by field_simp
  have hY : γ' * (A₂ / B₂) + δ' * (A / Bx) + ε' = (γ' * (A₂ * Bx) + δ' * (A * B₂) + ε' * (Bx * B₂)) / (Bx * B₂) := by
    field_simp
  refine ⟨hdX, mul_ne_zero hdX hdY, ?_, ?_⟩
  · rw [← hX, ← hY]; exact h₃
  · rw [key]; exact some_eq_some' hX hY

end WeierstrassCurve.VCTransport
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve.Affine.Point"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve.Affine.Point"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₁ map variableChange_a₃ a₄ a₂ variableChange_a₂ map_id toAffine Affine.Point variableChange_a₁ variableChange_a₄ VariableChange evalEvalBC IsRationallyRepresented rationalHomSet rationalEndSubring Affine.Point.equivOfVariableChangeEq"
namespace VCTransport
p2m_open "WeierstrassCurve"

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve.Affine WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve.Affine.Point"

def endConj {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : B ≃+ A) : AddMonoid.End A ≃+* AddMonoid.End B where
  toFun f := e.symm.toAddMonoidHom.comp (f.comp e.toAddMonoidHom)
  invFun g := e.toAddMonoidHom.comp (g.comp e.symm.toAddMonoidHom)
  left_inv f := by
    ext x
    show e (e.symm (f (e (e.symm x)))) = f x
    simp
  right_inv g := by
    ext x
    show e.symm (e (g (e.symm (e x)))) = g x
    simp
  map_mul' f g := by
    ext x
    show e.symm ((f * g) (e x)) = e.symm (f (e (e.symm (g (e x)))))
    rw [AddMonoid.End.coe_mul, Function.comp_apply, AddEquiv.apply_symm_apply]
  map_add' f g := by
    ext x
    show e.symm (f (e x) + g (e x)) = e.symm (f (e x)) + e.symm (g (e x))
    rw [map_add]

@[scoped simp] theorem endConj_apply {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : B ≃+ A) (f : AddMonoid.End A) (x : B) :
    endConj e f x = e.symm (f (e x)) := rfl

@[scoped simp] theorem endConj_symm_apply {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : B ≃+ A) (g : AddMonoid.End B) (x : A) :
    (endConj e).symm g x = e (g (e.symm x)) := rfl

variable {k : Type*} [Field k] [DecidableEq k]

theorem conj_mem_rationalHomSet (C : VariableChange k) (X : WeierstrassCurve k)
    {α : (X⁄k).Point →+ (X⁄k).Point} (hα : α ∈ rationalHomSet k X X) :
    (endConj (variableChangeAddEquiv C X) α : ((C • X)⁄k).Point →+ ((C • X)⁄k).Point) ∈ rationalHomSet k (C • X) (C • X) := by
  rcases hα with rfl | hα
  · left; ext P; rfl
  right
  have hu : (C.u : k) ≠ 0 := C.u.ne_zero
  refine isRationallyRepresented_conj (W₁ := X) (W₂ := C • X) hα (vcFun C X) (vcInvFun C X)
    ((C.u : k) ^ 2) C.r ((C.u : k) ^ 3) ((C.u : k) ^ 2 * C.s) C.t
    (((C.u⁻¹ : kˣ) : k) ^ 2) (-(((C.u⁻¹ : kˣ) : k) ^ 2 * C.r)) (((C.u⁻¹ : kˣ) : k) ^ 3) (-(((C.u⁻¹ : kˣ) : k) ^ 3 * C.s))
    (((C.u⁻¹ : kˣ) : k) ^ 3 * (C.s * C.r - C.t)) (pow_ne_zero _ hu) ?_ ?_ fun P => rfl
  · intro x y h
    exact ⟨(nonsingular_variableChange_iff x y).mp h, rfl⟩
  · intro x y h
    refine ⟨?_, ?_⟩
    swap
    · show Point.some (vcXInv C x) (vcYInv C x y) _ = _
      apply some_eq_some'' <;> simp only [vcXInv, vcYInv] <;> first | ring | skip
    · have h' : X.toAffine.Nonsingular (vcX C (vcXInv C x)) (vcY C (vcXInv C x) (vcYInv C x y)) := by
        rw [vcX_vcXInv, vcY_vcYInv]; exact h
      have h'' := (nonsingular_variableChange_iff (C := C) (W := X) _ _).mpr h'
      convert h'' using 1 <;> first | rfl | ring1 | (simp only [vcXInv, vcYInv, Units.val_inv_eq_inv_val]; ring1) | (simp only [vcXInv, vcYInv]; ring1)
where
  some_eq_some'' {W' : WeierstrassCurve.Affine k} {x₁ y₁ x₂ y₂ : k} {h₁ : W'.Nonsingular x₁ y₁} {h₂ : W'.Nonsingular x₂ y₂}
      (hx : x₁ = x₂) (hy : y₁ = y₂) : Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by subst hx hy; rfl

theorem conj_symm_mem_rationalHomSet (C : VariableChange k) (X : WeierstrassCurve k)
    {β : ((C • X)⁄k).Point →+ ((C • X)⁄k).Point} (hβ : β ∈ rationalHomSet k (C • X) (C • X)) :
    ((endConj (variableChangeAddEquiv C X)).symm β : (X⁄k).Point →+ (X⁄k).Point) ∈ rationalHomSet k X X := by
  rcases hβ with rfl | hβ
  · left; ext P; rfl
  right
  have hu : (C.u : k) ≠ 0 := C.u.ne_zero
  have hui : ((C.u⁻¹ : kˣ) : k) ≠ 0 := (C.u⁻¹).ne_zero
  refine isRationallyRepresented_conj (W₁ := C • X) (W₂ := X) hβ (vcInvFun C X) (vcFun C X)
    (((C.u⁻¹ : kˣ) : k) ^ 2) (-(((C.u⁻¹ : kˣ) : k) ^ 2 * C.r)) (((C.u⁻¹ : kˣ) : k) ^ 3) (-(((C.u⁻¹ : kˣ) : k) ^ 3 * C.s))
    (((C.u⁻¹ : kˣ) : k) ^ 3 * (C.s * C.r - C.t))
    ((C.u : k) ^ 2) C.r ((C.u : k) ^ 3) ((C.u : k) ^ 2 * C.s) C.t (pow_ne_zero _ hui) ?_ ?_ fun P => rfl
  · intro x y h
    refine ⟨?_, ?_⟩
    swap
    · show Point.some (vcXInv C x) (vcYInv C x y) _ = _
      apply conj_mem_rationalHomSet.some_eq_some'' <;> simp only [vcXInv, vcYInv] <;> first | ring | skip
    · have h' : X.toAffine.Nonsingular (vcX C (vcXInv C x)) (vcY C (vcXInv C x) (vcYInv C x y)) := by
        rw [vcX_vcXInv, vcY_vcYInv]; exact h
      have h'' := (nonsingular_variableChange_iff (C := C) (W := X) _ _).mpr h'
      convert h'' using 1 <;> first | rfl | ring1 | (simp only [vcXInv, vcYInv, Units.val_inv_eq_inv_val]; ring1) | (simp only [vcXInv, vcYInv]; ring1)
  · intro x y h
    exact ⟨(nonsingular_variableChange_iff x y).mp h, rfl⟩

theorem map_rationalEndSubring_eq (C : VariableChange k) (X : WeierstrassCurve k) :
    (rationalEndSubring k X).map (endConj (variableChangeAddEquiv C X)).toRingHom = rationalEndSubring k (C • X) := by
  apply le_antisymm
  · rw [Subring.map_le_iff_le_comap]
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    intro α hα
    exact Subring.subset_closure (conj_mem_rationalHomSet C X hα)
  · show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    intro β hβ
    refine ⟨(endConj (variableChangeAddEquiv C X)).symm β, ?_, by simp⟩
    exact Subring.subset_closure (conj_symm_mem_rationalHomSet C X hβ)

noncomputable def ringEquivOfVariableChange (C : VariableChange k) (X : WeierstrassCurve k) :
    ↥(rationalEndSubring k X) ≃+* ↥(rationalEndSubring k (C • X)) :=
  RingEquiv.trans ((endConj (variableChangeAddEquiv C X)).subringMap (s := rationalEndSubring k X))
    (RingEquiv.subringCongr (map_rationalEndSubring_eq C X))

theorem coe_ringEquivOfVariableChange (C : VariableChange k) (X : WeierstrassCurve k) (α : ↥(rationalEndSubring k X)) :
    ((ringEquivOfVariableChange C X α : ↥(rationalEndSubring k (C • X))) : AddMonoid.End ((C • X)⁄k).Point) =
      endConj (variableChangeAddEquiv C X) (α : AddMonoid.End (X⁄k).Point) := rfl

end WeierstrassCurve.VCTransport
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve.VCTransport"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve.Affine.Point"

open _root_.WeierstrassCurve _root_.P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve _root_.WeierstrassCurve.Affine _root_.P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve.Affine _root_.WeierstrassCurve.Affine.Point _root_.P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq.WeierstrassCurve.Affine.Point WeierstrassCurve.VCTransport in
theorem solution
    {k : Type*} [Field k] [DecidableEq k] (X Y : WeierstrassCurve k) (C : WeierstrassCurve.VariableChange k)
    (hC : C • X = Y) :
    ∃ φ : ↥(WeierstrassCurve.rationalEndSubring k X) ≃+* ↥(WeierstrassCurve.rationalEndSubring k Y),
      ∀ (α : ↥(WeierstrassCurve.rationalEndSubring k X)) (P : (Y⁄k).Point),
        ((φ α : ↥(WeierstrassCurve.rationalEndSubring k Y)) : AddMonoid.End (Y⁄k).Point) P =
          (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hC).symm
            ((α : AddMonoid.End (X⁄k).Point) (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hC P)) := by
  subst hC
  exact ⟨ringEquivOfVariableChange C X, fun α P => rfl⟩

end S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq
end P2MW
export P2MW.S_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq (solution)
