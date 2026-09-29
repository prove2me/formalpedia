-- Prove2me | solution 1 for WeierstrassCurve.natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_char_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/4d68d39f-2878-5c50-a0e1-c86bac8f6ee0

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_AddCommGroup_natCard_isAddCyclic_addSubgroup_map_eq_of_sq_eq_neg_one_eq_nuTwo
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_char_two
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open WeierstrassCurve WeierstrassCurve.Affine

namespace P2MKcFixI

section CharTwo

variable {K : Type*} [Field K] [CharP K 2]

theorem two_eq_zero : (2 : K) = 0 := by
  simpa using CharP.cast_eq_zero K 2

theorem three_eq_one : (3 : K) = 1 := by
  have : (3 : K) = 2 + 1 := by norm_num
  rw [this, two_eq_zero, zero_add]

theorem neg_eq (a : K) : -a = a := by
  have h : a + a = 0 := by rw [← two_mul, two_eq_zero, zero_mul]
  exact (neg_eq_of_add_eq_zero_left h)

theorem sub_eq_add' (a b : K) : a - b = a + b := by
  rw [sub_eq_add_neg, neg_eq]

theorem add_self (a : K) : a + a = 0 := by
  rw [← two_mul, two_eq_zero, zero_mul]

theorem sq_add (a b : K) : (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  have : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * (a * b) := by ring
  rw [this, two_eq_zero, zero_mul, add_zero]

theorem sq_add_self_eq_zero_iff (x : K) : x ^ 2 + x = 0 ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro h
    have : x * (x + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · right
      have := neg_eq (1 : K)
      linear_combination h1 + this
  · rintro (rfl | rfl)
    · ring
    · have := add_self (1 : K); simpa [sq] using this

variable (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
include hω

theorem omega_pow_three : ω ^ 3 = 1 := by
  have h1 : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
  rw [hω, mul_zero] at h1
  linear_combination -h1

theorem omega_ne_one : ω ≠ 1 := by
  intro h
  rw [h] at hω
  have : (3 : K) = 0 := by linear_combination hω
  rw [three_eq_one] at this
  exact one_ne_zero this

theorem omega_ne_zero : ω ≠ 0 := by
  intro h
  rw [h] at hω
  simp at hω

theorem omega_sq : ω ^ 2 = ω + 1 := by
  have h1 := neg_eq ω
  have h2 := neg_eq (1 : K)
  linear_combination hω + h1 + h2

theorem sq_add_self_add_one_eq_zero_iff (x : K) : x ^ 2 + x + 1 = 0 ↔ x = ω ∨ x = ω + 1 := by
  constructor
  · intro h
    have : (x + ω) * (x + ω + 1) = 0 := by
      have h2 := two_eq_zero (K := K)
      linear_combination h + hω + (x * ω - 1) * h2
    rcases mul_eq_zero.mp this with h0 | h1
    · left
      have := neg_eq ω
      linear_combination h0 + this
    · right
      have := neg_eq (ω + 1)
      linear_combination h1 + this
  · rintro (rfl | rfl)
    · exact hω
    · have h2 := two_eq_zero (K := K)
      linear_combination hω + (ω + 1) * h2

end CharTwo

section Curve

variable (K : Type*) [Field K] [CharP K 2]

def E₀ : WeierstrassCurve K := ⟨0, 0, 1, 0, 0⟩

@[scoped simp] theorem E₀_a₁ : (E₀ K).a₁ = 0 := rfl
@[scoped simp] theorem E₀_a₂ : (E₀ K).a₂ = 0 := rfl
@[scoped simp] theorem E₀_a₃ : (E₀ K).a₃ = 1 := rfl
@[scoped simp] theorem E₀_a₄ : (E₀ K).a₄ = 0 := rfl
@[scoped simp] theorem E₀_a₆ : (E₀ K).a₆ = 0 := rfl

theorem E₀_Δ : (E₀ K).Δ = 1 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, E₀_a₁, E₀_a₂, E₀_a₃, E₀_a₄, E₀_a₆]
  have h2 := two_eq_zero (K := K)
  linear_combination (-14 : K) * h2

scoped instance E₀_isElliptic : (E₀ K).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, E₀_Δ]; exact isUnit_one

theorem E₀_c₄ : (E₀ K).c₄ = 0 := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, E₀_a₁, E₀_a₂, E₀_a₃,
    E₀_a₄]
  ring

theorem E₀_j : (E₀ K).j = 0 := by
  rw [WeierstrassCurve.j, E₀_c₄]; ring

variable {K}

theorem smul_E₀_eq_iff (γ : VariableChange K) :
    γ • E₀ K = E₀ K ↔
      (γ.u : K) ^ 3 = 1 ∧ γ.r = γ.s ^ 2 ∧ γ.s ^ 4 = γ.s ∧ γ.t ^ 2 + γ.t = γ.s ^ 3 := by
  have h2 := two_eq_zero (K := K)
  have h3 := three_eq_one (K := K)
  have hu : (γ.u : K) ≠ 0 := γ.u.ne_zero
  have hui : ((γ.u⁻¹ : Kˣ) : K) * (γ.u : K) = 1 := by simp
  have hv : ((γ.u⁻¹ : Kˣ) : K) ≠ 0 := (γ.u⁻¹).ne_zero
  constructor
  · intro h
    have e₂ := congrArg WeierstrassCurve.a₂ h
    have e₃ := congrArg WeierstrassCurve.a₃ h
    have e₄ := congrArg WeierstrassCurve.a₄ h
    have e₆ := congrArg WeierstrassCurve.a₆ h
    simp only [E₀, variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆] at e₂ e₃ e₄ e₆

    have hv3 : ((γ.u⁻¹ : Kˣ) : K) ^ 3 = 1 := by
      linear_combination e₃ - ((γ.u⁻¹ : Kˣ) : K) ^ 3 * γ.t * h2
    have hu3 : (γ.u : K) ^ 3 = 1 := by
      have : ((γ.u⁻¹ : Kˣ) : K) ^ 3 * (γ.u : K) ^ 3 = 1 := by rw [← mul_pow, hui, one_pow]
      rwa [hv3, one_mul] at this

    have hr : γ.r = γ.s ^ 2 := by
      have : ((γ.u⁻¹ : Kˣ) : K) ^ 2 * ((3 : K) * γ.r - γ.s ^ 2) = 0 := by linear_combination e₂
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0) hv
      · rw [h3, one_mul, sub_eq_zero] at h0
        exact h0

    have hs : γ.s ^ 4 = γ.s := by
      have : ((γ.u⁻¹ : Kˣ) : K) ^ 4 * (-γ.s + (3 : K) * γ.r ^ 2 - 2 * γ.s * γ.t) = 0 := by
        linear_combination e₄
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd (pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h0) hv
      · rw [h3, h2, hr] at h0
        linear_combination h0

    have ht : γ.t ^ 2 + γ.t = γ.s ^ 3 := by
      have : ((γ.u⁻¹ : Kˣ) : K) ^ 6 * (γ.r ^ 3 - γ.t - γ.t ^ 2) = 0 := by linear_combination e₆
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd (pow_eq_zero_iff (n := 6) (by norm_num) |>.mp h0) hv
      · rw [hr] at h0
        have e : (γ.s ^ 2) ^ 3 = γ.s ^ 4 * γ.s ^ 2 := by ring
        rw [e, hs] at h0
        linear_combination -h0
    exact ⟨hu3, hr, hs, ht⟩
  · rintro ⟨hu3, hr, hs, ht⟩
    have hv3 : ((γ.u⁻¹ : Kˣ) : K) ^ 3 = 1 := by
      have : ((γ.u⁻¹ : Kˣ) : K) ^ 3 * (γ.u : K) ^ 3 = 1 := by rw [← mul_pow, hui, one_pow]
      rwa [hu3, mul_one] at this
    have hs3 : γ.s ^ 6 = γ.s ^ 3 := by
      calc γ.s ^ 6 = γ.s ^ 4 * γ.s ^ 2 := by ring
        _ = γ.s ^ 3 := by rw [hs]; ring
    have hns := neg_eq γ.s
    have hn1 := neg_eq γ.t
    have hn2 := neg_eq (γ.t ^ 2)
    have hss : γ.s + γ.s ^ 4 = 0 := by rw [hs, add_self]
    ext
    · simp only [variableChange_a₁, E₀]
      linear_combination ((γ.u⁻¹ : Kˣ) : K) * γ.s * h2
    · simp only [variableChange_a₂, E₀]
      rw [h3, hr]; ring
    · simp only [variableChange_a₃, E₀]
      linear_combination ((γ.u⁻¹ : Kˣ) : K) ^ 3 * γ.t * h2 + hv3
    · simp only [variableChange_a₄, E₀]
      rw [h2, h3, hr]
      linear_combination ((γ.u⁻¹ : Kˣ) : K) ^ 4 * hss - ((γ.u⁻¹ : Kˣ) : K) ^ 4 * γ.s * h2
    · simp only [variableChange_a₆, E₀]
      rw [hr]
      have : (γ.s ^ 2) ^ 3 - γ.t * 1 - γ.t ^ 2 = 0 := by
        have e : (γ.s ^ 2) ^ 3 = γ.s ^ 6 := by ring
        rw [e, hs3, ← ht]
        ring
      linear_combination ((γ.u⁻¹ : Kˣ) : K) ^ 6 * this

end Curve

section Explicit

variable {K : Type*} [Field K] [CharP K 2]

section MulComponents
variable {R : Type*} [CommRing R] (C C' : VariableChange R)
theorem mul_u : (C * C').u = C.u * C'.u := rfl
theorem mul_r : (C * C').r = C.r * (C'.u : R) ^ 2 + C'.r := rfl
theorem mul_s : (C * C').s = (C'.u : R) * C.s + C'.s := rfl
theorem mul_t : (C * C').t = C.t * (C'.u : R) ^ 3 + C.r * C'.s * (C'.u : R) ^ 2 + C'.t := rfl
end MulComponents

def ε : VariableChange K := ⟨1, 0, 0, 1⟩

theorem ε_smul : (ε : VariableChange K) • E₀ K = E₀ K :=
  (smul_E₀_eq_iff _).2 ⟨by simp [ε], by simp [ε], by simp [ε], by simpa [ε] using add_self (1 : K)⟩

variable (ω : K) (hω : ω ^ 2 + ω + 1 = 0)

def αv : VariableChange K := ⟨1, 1, 1, ω⟩

def δv : VariableChange K := ⟨1, ω ^ 2, ω, ω ^ 2⟩

include hω

def ωu : Kˣ := Units.mk0 ω (omega_ne_zero ω hω)

@[scoped simp] theorem coe_ωu : ((ωu ω hω : Kˣ) : K) = ω := rfl

def βv : VariableChange K := ⟨ωu ω hω, 0, 0, 0⟩

theorem αv_smul : αv ω • E₀ K = E₀ K :=
  (smul_E₀_eq_iff _).2 ⟨by simp [αv], by simp [αv], by simp [αv], by
    simp only [αv, one_pow]
    have := neg_eq (1 : K)
    linear_combination hω + this⟩

theorem βv_smul : βv ω hω • E₀ K = E₀ K :=
  (smul_E₀_eq_iff _).2 ⟨by simpa [βv] using omega_pow_three ω hω, by simp [βv], by simp [βv], by simp [βv]⟩

theorem δv_smul : δv ω • E₀ K = E₀ K := by
  have h3 := omega_pow_three ω hω
  have hsq := omega_sq ω hω
  refine (smul_E₀_eq_iff _).2 ⟨by simp [δv], by simp [δv], ?_, ?_⟩
  · show ω ^ 4 = ω
    calc ω ^ 4 = ω ^ 3 * ω := by ring
      _ = ω := by rw [h3, one_mul]
  · show (ω ^ 2) ^ 2 + ω ^ 2 = ω ^ 3
    rw [h3]
    have h2 := two_eq_zero (K := K)
    have : (ω ^ 2) ^ 2 = ω ^ 3 * ω := by ring
    rw [this, h3, one_mul, hsq]
    linear_combination ω * h2

theorem αv_mul_αv : αv ω * αv ω = ε := by
  ext
  · simp [mul_u, αv, ε]
  · simp only [mul_r, αv, ε, Units.val_one]; simpa using add_self (1 : K)
  · simp only [mul_s, αv, ε, Units.val_one]; simpa using add_self (1 : K)
  · simp only [mul_t, αv, ε, Units.val_one]
    have := add_self ω
    linear_combination this

theorem conj_αv_eq : βv ω hω * αv ω * (βv ω hω)⁻¹ = (⟨1, ω, ω ^ 2, ω⟩ : VariableChange K) := by
  have h3 := omega_pow_three ω hω
  have hne := omega_ne_zero ω hω
  have hinv : ω⁻¹ = ω ^ 2 := inv_eq_of_mul_eq_one_right (by
    calc ω * ω ^ 2 = ω ^ 3 := by ring
      _ = 1 := h3)
  have huinv : (((ωu ω hω)⁻¹ : Kˣ) : K) = ω ^ 2 := by
    rw [Units.val_inv_eq_inv_val, coe_ωu, hinv]
  have h4 : ω ^ 4 = ω := by
    calc ω ^ 4 = ω ^ 3 * ω := by ring
      _ = ω := by rw [h3, one_mul]
  have h7 : ω ^ 7 = ω := by
    calc ω ^ 7 = (ω ^ 3) ^ 2 * ω := by ring
      _ = ω := by rw [h3]; ring
  rw [VariableChange.inv_def]
  ext
  · simp [mul_u, αv, βv]
  · simp only [mul_r, mul_u, αv, βv, Units.val_mul, Units.val_one, coe_ωu, huinv]
    linear_combination h4
  · simp only [mul_s, mul_u, αv, βv, Units.val_mul, Units.val_one, coe_ωu, huinv]
    ring
  · simp only [mul_t, mul_r, mul_s, mul_u, αv, βv, Units.val_mul, Units.val_one, coe_ωu, huinv]
    linear_combination h7

theorem δv_eq : δv ω = αv ω * (βv ω hω * αv ω * (βv ω hω)⁻¹) := by
  rw [conj_αv_eq ω hω]
  have h2 := two_eq_zero (K := K)
  have hsq := omega_sq ω hω
  ext
  · simp [mul_u, αv, δv]
  · simp only [mul_r, αv, δv, Units.val_one]
    rw [hsq]; ring
  · simp only [mul_s, αv, δv, Units.val_one]
    have := neg_eq ω
    linear_combination -hω - this
  · simp only [mul_t, αv, δv, Units.val_one]
    linear_combination -ω * h2

theorem δv_mul_δv : δv ω * δv ω = (ε : VariableChange K) := by
  have h2 := two_eq_zero (K := K)
  have h3 := omega_pow_three ω hω
  ext
  · simp [mul_u, δv, ε]
  · simp only [mul_r, δv, ε, Units.val_one]
    linear_combination ω ^ 2 * h2
  · simp only [mul_s, δv, ε, Units.val_one]
    linear_combination ω * h2
  · simp only [mul_t, δv, ε, Units.val_one]
    linear_combination ω ^ 2 * h2 + h3

end Explicit

section Action

variable {K : Type*} [Field K] [CharP K 2] [DecidableEq K]

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

def castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) : W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

theorem heq_castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    HEq P (castPt e P) := by subst e; exact HEq.rfl

theorem xy_castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    xy (castPt e P) = xy P := by subst e; rfl

def act (γ : VariableChange K) (hγ : γ • E₀ K = E₀ K) : (E₀ K).toAffine.Point →+ (E₀ K).toAffine.Point :=
  (castPt hγ).toAddMonoidHom.comp
    { toFun := Point.vcInvFun γ (E₀ K).toAffine
      map_zero' := Point.vcInvFun_zero
      map_add' := Point.vcInvFun_add γ (E₀ K).toAffine }

theorem heq_act (γ : VariableChange K) (hγ : γ • E₀ K = E₀ K) (P : (E₀ K).toAffine.Point) :
    HEq (Point.vcInvFun γ (E₀ K).toAffine P) (act γ hγ P) :=
  heq_castPt _ _

theorem xy_act (γ : VariableChange K) (hγ : γ • E₀ K = E₀ K) (P : (E₀ K).toAffine.Point) :
    xy (act γ hγ P) = (xy P).map (fun q => (vcXInv γ q.1, vcYInv γ q.1 q.2)) := by
  show xy (castPt hγ (Point.vcInvFun γ (E₀ K).toAffine P)) = _
  rw [xy_castPt, xy_vcInvFun]

theorem act_injective (γ : VariableChange K) (hγ : γ • E₀ K = E₀ K) : Function.Injective (act γ hγ) := by
  intro P Q h
  have h' := congrArg xy h
  rw [xy_act, xy_act] at h'
  have hinj : Function.Injective (fun q : K × K => (vcXInv γ q.1, vcYInv γ q.1 q.2)) := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ hq
    simp only [Prod.mk.injEq] at hq
    obtain ⟨hx, hy⟩ := hq
    have hx' : x = x' := by simpa using congrArg (vcX γ) hx
    subst hx'
    have hy' : y = y' := by simpa using congrArg (vcY γ (vcXInv γ x)) hy
    exact Prod.ext rfl hy'
  exact xy_injective (Option.map_injective hinj h')

theorem act_mul (γ γ' : VariableChange K) (hγ : γ • E₀ K = E₀ K) (hγ' : γ' • E₀ K = E₀ K)
    (h : (γ * γ') • E₀ K = E₀ K) (P : (E₀ K).toAffine.Point) :
    act (γ * γ') h P = act γ hγ (act γ' hγ' P) := by
  apply xy_injective
  rw [xy_act, xy_act, xy_act]
  rcases P with _ | ⟨x, y, hP⟩
  · rfl
  · show some (vcXInv (γ * γ') x, vcYInv (γ * γ') x y) =
      some (vcXInv γ (vcXInv γ' x), vcYInv γ (vcXInv γ' x) (vcYInv γ' x y))
    have hu : (γ.u : K) ≠ 0 := γ.u.ne_zero
    have hu' : (γ'.u : K) ≠ 0 := γ'.u.ne_zero
    simp only [vcXInv, vcYInv, mul_u, mul_r, mul_s, mul_t, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val,
      Option.some.injEq, Prod.mk.injEq]
    constructor
    · field_simp; ring
    · field_simp; ring

theorem mul_smul_E₀ {γ γ' : VariableChange K} (hγ : γ • E₀ K = E₀ K) (hγ' : γ' • E₀ K = E₀ K) :
    (γ * γ') • E₀ K = E₀ K := by rw [mul_smul, hγ', hγ]

theorem inv_smul_E₀ {γ : VariableChange K} (hγ : γ • E₀ K = E₀ K) : γ⁻¹ • E₀ K = E₀ K := by
  rw [inv_smul_eq_iff, hγ]

theorem act_ε (P : (E₀ K).toAffine.Point) : act ε ε_smul P = -P := by
  apply xy_injective
  rw [xy_act]
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Point.neg_some]
    show some (vcXInv (ε : VariableChange K) x, vcYInv (ε : VariableChange K) x y) =
      some (x, (E₀ K).toAffine.negY x y)
    simp only [vcXInv, vcYInv, ε, inv_one, Units.val_one, one_pow, one_mul, sub_zero,
      zero_mul, WeierstrassCurve.Affine.negY, Option.some.injEq, Prod.mk.injEq, true_and]
    show y - 1 = -y - (E₀ K).a₁ * x - (E₀ K).a₃
    rw [E₀_a₁, E₀_a₃, neg_eq]; ring

theorem act_congr {γ γ' : VariableChange K} (h : γ = γ') (hγ : γ • E₀ K = E₀ K) (hγ' : γ' • E₀ K = E₀ K)
    (P : (E₀ K).toAffine.Point) : act γ hγ P = act γ' hγ' P := by subst h; rfl

theorem act_act_inv {γ : VariableChange K} (hγ : γ • E₀ K = E₀ K) (P : (E₀ K).toAffine.Point) :
    act γ hγ (act γ⁻¹ (inv_smul_E₀ hγ) P) = P := by
  rw [← act_mul γ γ⁻¹ hγ (inv_smul_E₀ hγ) (mul_smul_E₀ hγ (inv_smul_E₀ hγ))]
  rw [act_congr (mul_inv_cancel γ) _ (one_smul _ _)]
  apply xy_injective
  rw [xy_act]
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · show some (vcXInv (1 : VariableChange K) x, vcYInv (1 : VariableChange K) x y) = some (x, y)
    simp [vcXInv, vcYInv, VariableChange.one_def]

end Action

section NonScalar

variable {K : Type*} [Field K] [CharP K 2] [DecidableEq K]
variable (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
include hω

def σ : (E₀ K).toAffine.Point →+ (E₀ K).toAffine.Point := act (αv ω) (αv_smul ω hω)

theorem σ_apply (P : (E₀ K).toAffine.Point) : σ ω hω P = act (αv ω) (αv_smul ω hω) P := rfl

theorem σ_σ (P : (E₀ K).toAffine.Point) : σ ω hω (σ ω hω P) = -P := by
  rw [σ_apply, σ_apply, ← act_mul (αv ω) (αv ω) _ _ (mul_smul_E₀ (αv_smul ω hω) (αv_smul ω hω)) P,
    act_congr (αv_mul_αv ω hω) _ ε_smul, act_ε]

theorem δ_δ (P : (E₀ K).toAffine.Point) :
    act (δv ω) (δv_smul ω hω) (act (δv ω) (δv_smul ω hω) P) = -P := by
  rw [← act_mul (δv ω) (δv ω) _ _ (mul_smul_E₀ (δv_smul ω hω) (δv_smul ω hω)) P,
    act_congr (δv_mul_δv ω hω) _ ε_smul, act_ε]

theorem δ_eq_comp (P : (E₀ K).toAffine.Point) :
    act (δv ω) (δv_smul ω hω) P =
      σ ω hω (act (βv ω hω) (βv_smul ω hω)
        (σ ω hω (act (βv ω hω)⁻¹ (inv_smul_E₀ (βv_smul ω hω)) P))) := by
  have hβ := βv_smul ω hω
  have hα := αv_smul ω hω
  have hβi := inv_smul_E₀ hβ
  have h1 : (βv ω hω * αv ω) • E₀ K = E₀ K := mul_smul_E₀ hβ hα
  have h2 : (βv ω hω * αv ω * (βv ω hω)⁻¹) • E₀ K = E₀ K := mul_smul_E₀ h1 hβi
  have h3 : (αv ω * (βv ω hω * αv ω * (βv ω hω)⁻¹)) • E₀ K = E₀ K := mul_smul_E₀ hα h2
  rw [act_congr (δv_eq ω hω) _ h3, act_mul _ _ hα h2 h3, act_mul _ _ h1 hβi h2, act_mul _ _ hβ hα h1]
  rfl

omit hω in
theorem two_not_dvd_of_ne_zero {N : ℕ} (hN : (N : K) ≠ 0) : ¬2 ∣ N := by
  rintro ⟨c, rfl⟩
  apply hN
  push_cast
  rw [two_eq_zero, zero_mul]

theorem exists_addOrderOf_eq_and_ne_smul [IsAlgClosed K] (N : ℕ) (hN : (N : K) ≠ 0)
    (p : ℕ) (hp : p.Prime) (hpN : p ∣ N) :
    ∃ a : (E₀ K).toAffine.Point, addOrderOf a = p ∧ ∀ k : ℕ, σ ω hω a ≠ k • a := by
  have hp2 : p ≠ 2 := fun h => two_not_dvd_of_ne_zero hN (h ▸ hpN)
  have hN0 : N ≠ 0 := fun h => hN (by rw [h, Nat.cast_zero])
  haveI : NeZero N := ⟨hN0⟩
  obtain ⟨m, hm⟩ := hpN
  have hm0 : m ≠ 0 := fun h => hN0 (by rw [hm, h, mul_zero])
  have hp0 : p ≠ 0 := hp.ne_zero

  obtain ⟨e⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
    (F := K) (K := K) (E₀ K) (n := N) hN
  set T := Submodule.torsionBy ℤ (E₀ K).toAffine.Point N with hT
  let Φ : ZMod N × ZMod N →+ (E₀ K).toAffine.Point :=
    T.subtype.toAddMonoidHom.comp e.toAddMonoidHom
  have hΦ : ∀ x, Φ x = Subtype.val (e x) := fun x => rfl
  have hΦinj : Function.Injective Φ := Subtype.val_injective.comp e.injective

  have hordm : addOrderOf ((m : ℕ) : ZMod N) = p := by
    rw [ZMod.addOrderOf_coe m hN0, hm, Nat.gcd_mul_left_left, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have hord : ∀ x : ZMod N × ZMod N, addOrderOf (Φ x) = addOrderOf x := fun x =>
    addOrderOf_injective Φ hΦinj x
  set u₀ : (E₀ K).toAffine.Point := Φ ((m : ZMod N), 0) with hu₀
  set v₀ : (E₀ K).toAffine.Point := Φ (0, (m : ZMod N)) with hv₀
  have hou : addOrderOf u₀ = p := by
    rw [hu₀, hord, Prod.addOrderOf, hordm, addOrderOf_zero, Nat.lcm_one_right]
  have hov : addOrderOf v₀ = p := by
    rw [hv₀, hord, Prod.addOrderOf, hordm, addOrderOf_zero, Nat.lcm_one_left]
  have houv : addOrderOf (u₀ + v₀) = p := by
    rw [hu₀, hv₀, ← map_add, hord, Prod.mk_add_mk, add_zero, zero_add, Prod.addOrderOf, hordm, Nat.lcm_self]

  have hsmulΦ : ∀ (k : ℕ) (x : ZMod N × ZMod N), k • Φ x = Φ (k • x) := fun k x => (map_nsmul Φ k x).symm

  have hspan : ∀ a : (E₀ K).toAffine.Point, p • a = 0 → ∃ i j : ℕ, a = i • u₀ + j • v₀ := by
    intro a ha
    have haT : a ∈ T := by
      rw [hT, Submodule.mem_torsionBy_iff]
      show (N : ℤ) • a = 0
      rw [natCast_zsmul, hm, mul_nsmul, ha, nsmul_zero]
    obtain ⟨⟨x, y⟩, hxy⟩ : ∃ q : ZMod N × ZMod N, e q = ⟨a, haT⟩ := e.surjective _
    have haΦ : a = Φ (x, y) := by rw [hΦ, hxy]

    have hpxy : (p : ℕ) • (x, y) = 0 := by
      apply hΦinj
      rw [← hsmulΦ, ← haΦ, ha, map_zero]
    simp only [Prod.smul_mk, Prod.mk_eq_zero, nsmul_eq_mul] at hpxy
    obtain ⟨hpx, hpy⟩ := hpxy

    have hdiv : ∀ z : ZMod N, (p : ZMod N) * z = 0 → ∃ i : ℕ, z = i • ((m : ℕ) : ZMod N) := by
      intro z hz
      have hz' : ((p * z.val : ℕ) : ZMod N) = 0 := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val]; exact hz
      rw [ZMod.natCast_eq_zero_iff] at hz'
      have hz'' : p * m ∣ p * z.val := by rw [← hm]; exact hz'
      obtain ⟨i, hi⟩ := Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hp0) hz''
      refine ⟨i, ?_⟩
      rw [nsmul_eq_mul, ← Nat.cast_mul, mul_comm, ← hi, ZMod.natCast_zmod_val]
    obtain ⟨i, hi⟩ := hdiv x hpx
    obtain ⟨j, hj⟩ := hdiv y hpy
    refine ⟨i, j, ?_⟩
    rw [haΦ, hu₀, hv₀, hsmulΦ, hsmulΦ, ← map_add]
    congr 1
    rw [hi, hj]
    simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, zero_add]

  by_contra hall
  push Not at hall
  obtain ⟨k₁, hk₁⟩ := hall u₀ hou
  obtain ⟨k₂, hk₂⟩ := hall v₀ hov
  obtain ⟨k, hk⟩ := hall (u₀ + v₀) houv

  have hcomp : (((k₁ * m : ℕ) : ZMod N), ((k₂ * m : ℕ) : ZMod N)) =
      (((k * m : ℕ) : ZMod N), ((k * m : ℕ) : ZMod N)) := by
    apply hΦinj
    have : σ ω hω (u₀ + v₀) = k₁ • u₀ + k₂ • v₀ := by rw [map_add, hk₁, hk₂]
    rw [hk, smul_add] at this
    have e1 : k₁ • u₀ + k₂ • v₀ = Φ (((k₁ * m : ℕ) : ZMod N), ((k₂ * m : ℕ) : ZMod N)) := by
      rw [hu₀, hv₀, hsmulΦ, hsmulΦ, ← map_add]
      congr 1
      simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, zero_add, nsmul_eq_mul, Nat.cast_mul]
    have e2 : k • u₀ + k • v₀ = Φ (((k * m : ℕ) : ZMod N), ((k * m : ℕ) : ZMod N)) := by
      rw [hu₀, hv₀, hsmulΦ, hsmulΦ, ← map_add]
      congr 1
      simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, zero_add, nsmul_eq_mul, Nat.cast_mul]
    rw [← e1, ← e2, this]
  simp only [Prod.mk.injEq] at hcomp
  obtain ⟨hc₁, hc₂⟩ := hcomp
  have hσu : σ ω hω u₀ = k • u₀ := by
    rw [hk₁, hu₀, hsmulΦ, hsmulΦ]
    congr 1
    simp only [Prod.smul_mk, smul_zero, nsmul_eq_mul, Nat.cast_mul] at hc₁ ⊢
    rw [hc₁]
  have hσv : σ ω hω v₀ = k • v₀ := by
    rw [hk₂, hv₀, hsmulΦ, hsmulΦ]
    congr 1
    simp only [Prod.smul_mk, smul_zero, nsmul_eq_mul, Nat.cast_mul] at hc₂ ⊢
    rw [hc₂]

  have hpu : p • u₀ = 0 := by rw [← hou]; exact addOrderOf_nsmul_eq_zero u₀
  have hscalar : ∀ a : (E₀ K).toAffine.Point, p • a = 0 → σ ω hω a = k • a := by
    intro a ha
    obtain ⟨i, j, rfl⟩ := hspan a ha
    rw [map_add, map_nsmul, map_nsmul, hσu, hσv, smul_add, smul_comm i k, smul_comm j k]

  have hβ := βv_smul ω hω
  have hσ' : act (βv ω hω) hβ (σ ω hω (act (βv ω hω)⁻¹ (inv_smul_E₀ hβ) u₀)) = k • u₀ := by
    have hw : p • act (βv ω hω)⁻¹ (inv_smul_E₀ hβ) u₀ = 0 := by rw [← map_nsmul, hpu, map_zero]
    rw [hscalar _ hw, map_nsmul, act_act_inv]

  have hδu : act (δv ω) (δv_smul ω hω) u₀ = k • (k • u₀) := by
    rw [δ_eq_comp ω hω, hσ', map_nsmul, hσu]
  have hkk : k • (k • u₀) = -u₀ := by
    rw [← σ_σ ω hω u₀, hσu, map_nsmul, hσu]
  have hδδ : act (δv ω) (δv_smul ω hω) (act (δv ω) (δv_smul ω hω) u₀) = u₀ := by
    rw [hδu, map_nsmul, map_nsmul, hδu, hkk, smul_neg, smul_neg, hkk, neg_neg]
  rw [δ_δ ω hω u₀] at hδδ

  have h2u : 2 • u₀ = 0 := by
    rw [two_nsmul]
    nth_rewrite 1 [← hδδ]
    rw [neg_add_cancel]
  have hp2' : p ∣ 2 := hou ▸ addOrderOf_dvd_of_nsmul_eq_zero h2u
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2')

end NonScalar

section Count

variable {K : Type*} [Field K] [CharP K 2] [DecidableEq K] [IsAlgClosed K]
variable (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
include hω

theorem main (N : ℕ) (hN : (N : K) ≠ 0) :
    Nat.card {H : AddSubgroup (E₀ K).toAffine.Point //
        IsAddCyclic H ∧ Nat.card H = N ∧
        ∀ T ∈ H, ∃ T' ∈ H, HEq (Point.vcInvFun (αv ω) (E₀ K).toAffine T) T'}
      = ModularCurve.nuTwo N := by
  have hN0 : N ≠ 0 := fun h => hN (by rw [h, Nat.cast_zero])
  haveI : NeZero N := ⟨hN0⟩
  obtain ⟨e⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
    (F := K) (K := K) (E₀ K) (n := N) hN
  have hcore := AddCommGroup.natCard_isAddCyclic_addSubgroup_map_eq_of_sq_eq_neg_one_eq_nuTwo
    (A := (E₀ K).toAffine.Point) N e
    (σ ω hω) (σ_σ ω hω) (fun p hp hpN => exists_addOrderOf_eq_and_ne_smul ω hω N hN p hp hpN)
  rw [← hcore]
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight fun H => ?_
  refine and_congr_right fun hcyc => and_congr_right fun hcard => ?_
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hN0)
  constructor
  · intro h
    have hle : H.map (σ ω hω) ≤ H := by
      rintro _ ⟨T, hT, rfl⟩
      obtain ⟨T', hT', hh⟩ := h T hT
      have : σ ω hω T = T' := eq_of_heq ((heq_act (αv ω) (αv_smul ω hω) T).symm.trans hh)
      show σ ω hω T ∈ H
      rw [this]; exact hT'
    exact @AddSubgroup.eq_of_le_of_card_ge _ _ _ _ this hle
      (by rw [AddSubgroup.card_map_of_injective (act_injective _ _)])
  · intro h T hT
    refine ⟨σ ω hω T, ?_, heq_act (αv ω) (αv_smul ω hω) T⟩
    rw [← h]
    exact AddSubgroup.mem_map_of_mem _ hT

end Count

end P2MKcFixI
p2m_reactivate "P2MW.S_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_char_two.P2MKcFixI"

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve in
theorem solution
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] [CharP L 2]
    (ω : L) (hω : ω ^ 2 + ω + 1 = 0) (N : ℕ) (hN : (N : L) ≠ 0) :
    Nat.card {H : AddSubgroup (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point //
        IsAddCyclic H ∧ Nat.card H = N ∧
        ∀ T ∈ H, ∃ T' ∈ H, HEq (Point.vcInvFun (⟨1, 1, 1, ω⟩ : VariableChange L)
          (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine T) T'}
      = nuTwo N :=
  P2MKcFixI.main ω hω N hN

end S_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_char_two
end P2MW
export P2MW.S_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_char_two (solution)
