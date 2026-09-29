-- Prove2me | solution 1 for WeierstrassCurve.exists_addMonoidHom_i_tau_vcInvFun_of_char_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/c368f8f6-d2c2-54ff-a644-d939dbbe0beb

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_addMonoidHom_i_tau_vcInvFun_of_char_three

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 6400000

open WeierstrassCurve WeierstrassCurve.Affine

namespace P2MKcAutE0

variable {K : Type*} [Field K] [DecidableEq K]

def xy {W : WeierstrassCurve K} : W.toAffine.Point → Option (K × K)
  | 0 => none
  | .some x y _ => some (x, y)

theorem xy_injective {W : WeierstrassCurve K} : Function.Injective (xy (W := W)) := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hh
  · rfl
  · exact absurd hh (by simp [xy])
  · exact absurd hh (by simp [xy])
  · simp only [xy, Option.some.injEq, Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    rfl

theorem xy_vcInvFun (γ : VariableChange K) {W : WeierstrassCurve K} (P : W.toAffine.Point) :
    xy (Point.vcInvFun γ W.toAffine P) = (xy P).map (fun q => (vcXInv γ q.1, vcYInv γ q.1 q.2)) := by
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

theorem xy_neg {W : WeierstrassCurve K} (P : W.toAffine.Point) :
    xy (-P) = (xy P).map (fun q => (q.1, W.toAffine.negY q.1 q.2)) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Affine.Point.neg_some]; rfl

theorem exists_eq_some_of_xy_eq {W : WeierstrassCurve K} {Q : W.toAffine.Point} {x y : K}
    (h : xy Q = some (x, y)) : ∃ h', Q = Point.some x y h' := by
  rcases Q with _ | ⟨x', y', h'⟩
  · exact absurd h (by simp [xy])
  · simp only [xy, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨h', rfl⟩

def castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) : W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

theorem heq_castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    HEq P (castPt e P) := by subst e; exact HEq.rfl

theorem xy_castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    xy (castPt e P) = xy P := by subst e; rfl

noncomputable def vcHom (γ : VariableChange K) (W : WeierstrassCurve K) (hW : γ • W = W) :
    W.toAffine.Point →+ W.toAffine.Point :=
  (castPt hW).toAddMonoidHom.comp
    { toFun := Point.vcInvFun γ W.toAffine
      map_zero' := Point.vcInvFun_zero
      map_add' := Point.vcInvFun_add γ W.toAffine }

theorem vcHom_apply (γ : VariableChange K) (W : WeierstrassCurve K) (hW : γ • W = W)
    (P : W.toAffine.Point) : vcHom γ W hW P = castPt hW (Point.vcInvFun γ W.toAffine P) := rfl

theorem heq_vcHom (γ : VariableChange K) (W : WeierstrassCurve K) (hW : γ • W = W)
    (P : W.toAffine.Point) : HEq (Point.vcInvFun γ W.toAffine P) (vcHom γ W hW P) :=
  heq_castPt hW _

theorem xy_vcHom (γ : VariableChange K) (W : WeierstrassCurve K) (hW : γ • W = W)
    (P : W.toAffine.Point) :
    xy (vcHom γ W hW P) = (xy P).map (fun q => (vcXInv γ q.1, vcYInv γ q.1 q.2)) := by
  rw [vcHom_apply, xy_castPt, xy_vcInvFun]

theorem heq_of_xy_eq {W : WeierstrassCurve K} (γ : VariableChange K) (hW : γ • W = W)
    (T : W.toAffine.Point) (Q : W.toAffine.Point)
    (h : (xy T).map (fun q => (vcXInv γ q.1, vcYInv γ q.1 q.2)) = xy Q) :
    HEq (Point.vcInvFun γ W.toAffine T) Q := by
  have h1 : castPt hW (Point.vcInvFun γ W.toAffine T) = Q := by
    apply xy_injective
    rw [xy_castPt, xy_vcInvFun, h]
  exact (heq_castPt hW _).trans (h1 ▸ HEq.rfl)

section CharThree

variable [CharP K 3]

theorem three_eq_zero : (3 : K) = 0 := by simpa using CharP.cast_eq_zero K 3

theorem two_eq_neg_one : (2 : K) = -1 := by
  have h3 : (3 : K) = 0 := three_eq_zero
  linear_combination h3

theorem two_ne_zero' : (2 : K) ≠ 0 := by
  rw [two_eq_neg_one]; exact neg_ne_zero.mpr one_ne_zero

abbrev E0 (K : Type*) [Field K] : WeierstrassCurve K := ⟨0, 0, 0, -1, 0⟩

theorem stab_iff (γ : VariableChange K) :
    γ • E0 K = E0 K ↔ γ.s = 0 ∧ γ.t = 0 ∧ (γ.u : K) ^ 4 = 1 ∧ γ.r ^ 3 = γ.r := by
  have h3 : (3 : K) = 0 := three_eq_zero
  have h2 : (2 : K) ≠ 0 := two_ne_zero'
  have hu : (γ.u : K) ≠ 0 := γ.u.ne_zero
  have hui : ((γ.u⁻¹ : Kˣ) : K) = (γ.u : K)⁻¹ := Units.val_inv_eq_inv_val _
  have hui0 : ((γ.u⁻¹ : Kˣ) : K) ≠ 0 := (γ.u⁻¹).ne_zero
  constructor
  · intro h
    have h1 := congrArg WeierstrassCurve.a₁ h
    have h3' := congrArg WeierstrassCurve.a₃ h
    have h4 := congrArg WeierstrassCurve.a₄ h
    have h6 := congrArg WeierstrassCurve.a₆ h
    simp only [variableChange_a₁, variableChange_a₃, variableChange_a₄, variableChange_a₆] at h1 h3' h4 h6
    have hs : γ.s = 0 := by
      have : ((γ.u⁻¹ : Kˣ) : K) * (2 * γ.s) = 0 := by simpa using h1
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hui0
      · exact (mul_eq_zero.mp h).resolve_left h2
    have ht : γ.t = 0 := by
      have : ((γ.u⁻¹ : Kˣ) : K) ^ 3 * (2 * γ.t) = 0 := by simpa [hs] using h3'
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (pow_ne_zero _ hui0)
      · exact (mul_eq_zero.mp h).resolve_left h2
    simp only [hs, ht, mul_zero, zero_mul, sub_zero, add_zero, zero_add] at h4 h6
    refine ⟨hs, ht, ?_, ?_⟩
    ·
      have h4' : ((γ.u⁻¹ : Kˣ) : K) ^ 4 * (-1 + 3 * γ.r ^ 2) = -1 := by
        linear_combination h4
      rw [h3, zero_mul, add_zero, mul_neg_one, neg_inj, hui] at h4'
      have : (γ.u : K) ^ 4 * ((γ.u : K)⁻¹) ^ 4 = 1 := by field_simp
      rw [h4', mul_one] at this
      exact this
    ·
      have h6' : ((γ.u⁻¹ : Kˣ) : K) ^ 6 * (-γ.r + γ.r ^ 3) = 0 := by
        linear_combination h6
      rcases mul_eq_zero.mp h6' with h | h
      · exact absurd h (pow_ne_zero _ hui0)
      · linear_combination h
  · rintro ⟨hs, ht, hu4, hr3⟩
    have hui4 : ((γ.u⁻¹ : Kˣ) : K) ^ 4 = 1 := by
      rw [hui, inv_pow, hu4, inv_one]
    have hui6 : ((γ.u⁻¹ : Kˣ) : K) ^ 6 = ((γ.u⁻¹ : Kˣ) : K) ^ 2 := by
      rw [show (6 : ℕ) = 4 + 2 by norm_num, pow_add, hui4, one_mul]
    ext
    · simp [variableChange_a₁, hs]
    · simp [variableChange_a₂, hs, h3]
    · simp [variableChange_a₃, hs, ht]
    · simp only [variableChange_a₄, hs, ht]
      ring_nf
      rw [hui4]; linear_combination (-(3 : K) * γ.r ^ 2 + 3 * γ.r ^ 2) * hui4 + γ.r ^ 2 * h3
    · simp only [variableChange_a₆, hs, ht]
      ring_nf
      linear_combination ((γ.u⁻¹ : Kˣ) : K) ^ 6 * hr3

theorem mk_stab (v : Kˣ) (hv : (v : K) ^ 4 = 1) (ρ : K) (hρ : ρ ^ 3 = ρ) :
    (⟨v, ρ, 0, 0⟩ : VariableChange K) • E0 K = E0 K :=
  (stab_iff _).mpr ⟨rfl, rfl, hv, hρ⟩

def SixForm (v : Kˣ) (ρ : K) (m : (E0 K).toAffine.Point →+ (E0 K).toAffine.Point) : Prop :=
  ∀ P, xy (m P) = (xy P).map fun q => (((v⁻¹ : Kˣ) : K) ^ 2 * (q.1 - ρ), ((v⁻¹ : Kˣ) : K) ^ 3 * q.2)

theorem heq_pos {v : Kˣ} {ρ : K} {m : (E0 K).toAffine.Point →+ (E0 K).toAffine.Point}
    (hm : SixForm v ρ m) (hst : (⟨v, ρ, 0, 0⟩ : VariableChange K) • E0 K = E0 K) (T : (E0 K).toAffine.Point) :
    HEq (Point.vcInvFun (⟨v, ρ, 0, 0⟩ : VariableChange K) (E0 K).toAffine T) (m T) := by
  apply heq_of_xy_eq _ hst
  rw [hm T]
  rcases T with _ | ⟨x, y, h⟩
  · rfl
  · simp [xy, vcXInv, vcYInv]

theorem heq_neg {v : Kˣ} {ρ : K} {m : (E0 K).toAffine.Point →+ (E0 K).toAffine.Point}
    (hm : SixForm v ρ m) (hst : (⟨-v, ρ, 0, 0⟩ : VariableChange K) • E0 K = E0 K) (T : (E0 K).toAffine.Point) :
    HEq (Point.vcInvFun (⟨-v, ρ, 0, 0⟩ : VariableChange K) (E0 K).toAffine T) (-(m T)) := by
  apply heq_of_xy_eq _ hst
  rw [xy_neg, hm T]
  rcases T with _ | ⟨x, y, h⟩
  · rfl
  · simp only [xy, Option.map_some, vcXInv, vcYInv, Affine.negY, inv_neg, Units.val_neg,
      Option.some.injEq, Prod.mk.injEq]
    constructor <;> ring

theorem stab_case (γ : VariableChange K) (hγ : γ • E0 K = E0 K) (hs : γ.s = 0) (ht : γ.t = 0)
    (v : Kˣ) (ρ : K) (m : (E0 K).toAffine.Point →+ (E0 K).toAffine.Point) (hm : SixForm v ρ m)
    (hr : γ.r = ρ) (hu : (γ.u : K) = v ∨ (γ.u : K) = -v) :
    (∀ T, HEq (Point.vcInvFun γ (E0 K).toAffine T) (m T)) ∨
      (∀ T, HEq (Point.vcInvFun γ (E0 K).toAffine T) (-(m T))) := by
  obtain ⟨u, r, s, t⟩ := γ
  simp only at hs ht hr hu
  subst hs ht hr
  rcases hu with hu | hu
  · have : u = v := Units.ext hu
    subst this
    exact Or.inl (heq_pos hm hγ)
  · have : u = -v := Units.ext (by rw [hu, Units.val_neg])
    subst this
    exact Or.inr (heq_neg hm hγ)

variable (i : Kˣ) (hi : (i : K) ^ 2 = -1)

include hi in
theorem i_pow_four : (i : K) ^ 4 = 1 := by
  have : (i : K) ^ 4 = ((i : K) ^ 2) ^ 2 := by ring
  rw [this, hi]; norm_num

include hi in
theorem i_inv : ((i⁻¹ : Kˣ) : K) = -(i : K) := by
  rw [Units.val_inv_eq_inv_val]
  apply inv_eq_of_mul_eq_one_right
  linear_combination (-1 : K) * hi

include hi in
theorem i_inv_sq : ((i⁻¹ : Kˣ) : K) ^ 2 = -1 := by rw [i_inv i hi, neg_sq, hi]

include hi in
theorem i_inv_cube : ((i⁻¹ : Kˣ) : K) ^ 3 = (i : K) := by
  rw [i_inv i hi]
  linear_combination (-(i : K)) * hi

theorem one_inv_val : (((1 : Kˣ)⁻¹ : Kˣ) : K) = 1 := by simp

theorem zero_cube : (0 : K) ^ 3 = 0 := by norm_num
theorem one_cube : (1 : K) ^ 3 = 1 := by norm_num
theorem neg_one_cube : (-1 : K) ^ 3 = -1 := by norm_num
theorem one_pow_four' : ((1 : Kˣ) : K) ^ 4 = 1 := by simp

include hi in
theorem hαγ : (⟨i, 0, 0, 0⟩ : VariableChange K) • E0 K = E0 K := mk_stab i (i_pow_four i hi) 0 zero_cube

theorem hβγ : (⟨1, 1, 0, 0⟩ : VariableChange K) • E0 K = E0 K := mk_stab 1 one_pow_four' 1 one_cube

noncomputable def αH : (E0 K).toAffine.Point →+ (E0 K).toAffine.Point := vcHom ⟨i, 0, 0, 0⟩ (E0 K) (hαγ i hi)

noncomputable def βH : (E0 K).toAffine.Point →+ (E0 K).toAffine.Point := vcHom ⟨1, 1, 0, 0⟩ (E0 K) hβγ

theorem xy_α (P : (E0 K).toAffine.Point) :
    xy (αH i hi P) = (xy P).map fun q => (-q.1, (i : K) * q.2) := by
  rw [αH, xy_vcHom]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, vcXInv, vcYInv, i_inv_sq i hi, i_inv_cube i hi, Option.some.injEq,
      Prod.mk.injEq]
    constructor <;> ring

theorem xy_β (P : (E0 K).toAffine.Point) :
    xy (βH (K := K) P) = (xy P).map fun q => (q.1 - 1, q.2) := by
  rw [βH, xy_vcHom]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp [vcXInv, vcYInv]

theorem αα (T : (E0 K).toAffine.Point) : αH i hi (αH i hi T) = -T := by
  apply xy_injective
  rw [xy_α, xy_α, xy_neg]
  rcases xy T with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, Affine.negY, Option.some.injEq, Prod.mk.injEq]
    constructor
    · ring
    · linear_combination y * hi

theorem αβ (T : (E0 K).toAffine.Point) : αH i hi (βH T) = βH (βH (αH i hi T)) := by
  apply xy_injective
  rw [xy_α, xy_β, xy_β, xy_β, xy_α]
  rcases xy T with _ | ⟨x, y⟩
  · rfl
  · have h3 : (3 : K) = 0 := three_eq_zero
    have hx : (-(x - 1) : K) = -x - 1 - 1 := by linear_combination h3
    simp only [Option.map_some, hx]

theorem ββ1 (T : (E0 K).toAffine.Point) : βH (βH T) + βH T + T = 0 := by
  have h3 : (3 : K) = 0 := three_eq_zero
  rcases T with _ | ⟨x, y, h⟩
  · change βH (βH 0) + βH 0 + (0 : (E0 K).toAffine.Point) = 0
    simp only [map_zero, add_zero]
  · have hβ : xy (βH (K := K) (Point.some x y h)) = some (x - 1, y) := by rw [xy_β]; rfl
    have hββ : xy (βH (βH (K := K) (Point.some x y h))) = some (x - 1 - 1, y) := by rw [xy_β, xy_β]; rfl
    obtain ⟨h₁, e₁⟩ := exists_eq_some_of_xy_eq hβ
    obtain ⟨h₂, e₂⟩ := exists_eq_some_of_xy_eq hββ
    rw [e₂, e₁]
    have hne : x - 1 - 1 ≠ x - 1 := by
      intro hx
      have : (1 : K) = 0 := by linear_combination -hx
      exact one_ne_zero this
    rw [Affine.Point.add_of_X_ne hne]

    have hsum : xy (Point.some _ _ (nonsingular_add h₂ h₁ fun hxy => hne hxy.left) :
        (E0 K).toAffine.Point) = xy (-(Point.some x y h) : (E0 K).toAffine.Point) := by
      rw [xy_neg]
      simp only [xy, Option.map_some, Affine.addX, Affine.addY, Affine.negAddY, Affine.negY,
        Affine.slope_of_X_ne hne, sub_self, zero_div, Option.some.injEq, Prod.mk.injEq]
      constructor
      · linear_combination (1 - x) * h3
      · linear_combination (-(0 : K)) * h3
    rw [xy_injective hsum, neg_add_cancel]

theorem sixForm_id : SixForm (K := K) 1 0 (AddMonoidHom.id _) := by
  intro P
  rw [AddMonoidHom.id_apply]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, inv_one, Units.val_one, one_pow, one_mul, sub_zero]

theorem sixForm_α : SixForm i 0 (αH i hi) := by
  intro P
  rw [xy_α]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · have hx : (-x : K) = -1 * (x - 0) := by ring
    simp only [Option.map_some, i_inv_sq i hi, i_inv_cube i hi, hx]

theorem sixForm_β : SixForm (K := K) 1 1 βH := by
  intro P
  rw [xy_β]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, inv_one, Units.val_one, one_pow, one_mul]

theorem sixForm_ββ : SixForm (K := K) 1 (-1) (βH.comp βH) := by
  intro P
  have h3 : (3 : K) = 0 := three_eq_zero
  rw [AddMonoidHom.comp_apply, xy_β, xy_β]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · have hx : (x - 1 - 1 : K) = x - -1 := by linear_combination -h3
    simp only [Option.map_some, inv_one, Units.val_one, one_pow, one_mul, hx]

theorem sixForm_αβ : SixForm i 1 ((αH i hi).comp βH) := by
  intro P
  rw [AddMonoidHom.comp_apply, xy_α, xy_β]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · have hx : (-(x - 1) : K) = -1 * (x - 1) := by ring
    simp only [Option.map_some, i_inv_sq i hi, i_inv_cube i hi, hx]

theorem sixForm_αββ : SixForm i (-1) ((αH i hi).comp (βH.comp βH)) := by
  intro P
  have h3 : (3 : K) = 0 := three_eq_zero
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, xy_α, xy_β, xy_β]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · have hx : (-(x - 1 - 1) : K) = -1 * (x - -1) := by linear_combination h3
    simp only [Option.map_some, i_inv_sq i hi, i_inv_cube i hi, hx]

include hi in
theorem u_cases (u : Kˣ) (hu4 : (u : K) ^ 4 = 1) :
    ((u : K) = (1 : Kˣ) ∨ (u : K) = -(1 : Kˣ)) ∨ ((u : K) = i ∨ (u : K) = -i) := by
  have h : ((u : K) ^ 2 - 1) * ((u : K) ^ 2 - (i : K) ^ 2) = 0 := by
    rw [hi]; linear_combination hu4
  rcases mul_eq_zero.mp h with h | h
  · left
    have : ((u : K) - 1) * ((u : K) + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · left; rw [Units.val_one]; linear_combination h'
    · right; rw [Units.val_one]; linear_combination h'
  · right
    have : ((u : K) - i) * ((u : K) + i) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · left; linear_combination h'
    · right; linear_combination h'

theorem r_cases (r : K) (hr : r ^ 3 = r) : r = 0 ∨ r = 1 ∨ r = -1 := by
  have : r * ((r - 1) * (r + 1)) = 0 := by linear_combination hr
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inr (Or.inl (by linear_combination h))
    · exact Or.inr (Or.inr (by linear_combination h))

end CharThree

end P2MKcAutE0

open P2MKcAutE0 in
theorem solution
    {K : Type*} [Field K] [DecidableEq K] [CharP K 3] (i : Kˣ) (hi : (i : K) ^ 2 = -1) :
    ∃ α β : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point →+
        (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point,
      (∀ T, HEq (Point.vcInvFun (⟨i, 0, 0, 0⟩ : VariableChange K)
          (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine T) (α T)) ∧
      (∀ T, HEq (Point.vcInvFun (⟨1, 1, 0, 0⟩ : VariableChange K)
          (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine T) (β T)) ∧
      (∀ T, α (α T) = -T) ∧ (∀ T, β (β T) + β T + T = 0) ∧ (∀ T, α (β T) = β (β (α T))) ∧
      (∀ γ : VariableChange K,
          γ • (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K) = ⟨0, 0, 0, -1, 0⟩ →
        ∃ m : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point →+
            (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point,
          (m = AddMonoidHom.id _ ∨ m = α ∨ m = β ∨ m = β.comp β ∨ m = α.comp β ∨
              m = α.comp (β.comp β)) ∧
          ((∀ T, HEq (Point.vcInvFun γ (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine T) (m T)) ∨
            (∀ T, HEq (Point.vcInvFun γ (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine T)
              (-(m T))))) ∧
      (∀ m : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point →+
            (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point,
          (m = AddMonoidHom.id _ ∨ m = α ∨ m = β ∨ m = β.comp β ∨ m = α.comp β ∨
              m = α.comp (β.comp β)) →
        ∃ γ : VariableChange K, γ • (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K) = ⟨0, 0, 0, -1, 0⟩ ∧
          ∀ T, HEq (Point.vcInvFun γ (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine T) (m T)) := by
  refine ⟨αH i hi, βH, heq_vcHom _ _ _, heq_vcHom _ _ _, αα i hi, ββ1, αβ i hi, ?_, ?_⟩
  ·
    intro γ hγ
    obtain ⟨hs, ht, hu4, hr3⟩ := (stab_iff γ).mp hγ
    rcases u_cases i hi γ.u hu4 with hu | hu <;> rcases r_cases γ.r hr3 with hr | hr | hr
    · exact ⟨_, Or.inl rfl, stab_case γ hγ hs ht 1 0 _ sixForm_id hr hu⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), stab_case γ hγ hs ht 1 1 _ sixForm_β hr hu⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inl rfl))), stab_case γ hγ hs ht 1 (-1) _ sixForm_ββ hr hu⟩
    · exact ⟨_, Or.inr (Or.inl rfl), stab_case γ hγ hs ht i 0 _ (sixForm_α i hi) hr hu⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
        stab_case γ hγ hs ht i 1 _ (sixForm_αβ i hi) hr hu⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))),
        stab_case γ hγ hs ht i (-1) _ (sixForm_αββ i hi) hr hu⟩
  ·
    intro m hm
    have hi4 := i_pow_four i hi
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨1, 0, 0, 0⟩, mk_stab 1 one_pow_four' 0 zero_cube,
        heq_pos sixForm_id (mk_stab 1 one_pow_four' 0 zero_cube)⟩
    · exact ⟨⟨i, 0, 0, 0⟩, hαγ i hi, heq_pos (sixForm_α i hi) (hαγ i hi)⟩
    · exact ⟨⟨1, 1, 0, 0⟩, hβγ, heq_pos sixForm_β hβγ⟩
    · exact ⟨⟨1, -1, 0, 0⟩, mk_stab 1 one_pow_four' (-1) neg_one_cube,
        heq_pos sixForm_ββ (mk_stab 1 one_pow_four' (-1) neg_one_cube)⟩
    · exact ⟨⟨i, 1, 0, 0⟩, mk_stab i hi4 1 one_cube, heq_pos (sixForm_αβ i hi) (mk_stab i hi4 1 one_cube)⟩
    · exact ⟨⟨i, -1, 0, 0⟩, mk_stab i hi4 (-1) neg_one_cube,
        heq_pos (sixForm_αββ i hi) (mk_stab i hi4 (-1) neg_one_cube)⟩

end S_WeierstrassCurve_exists_addMonoidHom_i_tau_vcInvFun_of_char_three
end P2MW
export P2MW.S_WeierstrassCurve_exists_addMonoidHom_i_tau_vcInvFun_of_char_three (solution)
