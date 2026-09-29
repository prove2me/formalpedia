-- Prove2me | solution 1 for WeierstrassCurve.exists_addMonoidHom_omega_i_j_vcInvFun_of_char_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/6f49285c-0c74-5885-bbcc-ee2030b956c7

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_addMonoidHom_omega_i_j_vcInvFun_of_char_two
set_option Elab.async false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace AutCurveCharTwo

variable {K : Type*} [Field K]

section Coordinates

private def xy {W : WeierstrassCurve K} : W.toAffine.Point → Option (K × K)
  | 0 => none
  | .some x y _ => some (x, y)

private theorem xy_injective {W : WeierstrassCurve K} : Function.Injective (xy (W := W)) := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hh
  · rfl
  · exact absurd hh (by simp [xy])
  · exact absurd hh (by simp [xy])
  · simp only [xy, Option.some.injEq, Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    rfl

private theorem xy_vcInvFun (γ : VariableChange K) {W : WeierstrassCurve K} (P : W.toAffine.Point) :
    xy (Point.vcInvFun γ W.toAffine P) =
      (xy P).map (fun q => (vcXInv γ q.1, vcYInv γ q.1 q.2)) := by
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

private theorem xy_neg {W : WeierstrassCurve K} (P : W.toAffine.Point) :
    xy (-P) = (xy P).map (fun q => (q.1, W.toAffine.negY q.1 q.2)) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Affine.Point.neg_some]; rfl

end Coordinates

section Transport
variable [DecidableEq K]

private def castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) :
    W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

private theorem heq_castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    HEq P (castPt e P) := by subst e; exact HEq.rfl

private theorem xy_castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    xy (castPt e P) = xy P := by subst e; rfl

private noncomputable def vcHom (γ : VariableChange K) (W : WeierstrassCurve K) (hW : γ • W = W) :
    W.toAffine.Point →+ W.toAffine.Point :=
  (castPt hW).toAddMonoidHom.comp
    { toFun := Point.vcInvFun γ W.toAffine
      map_zero' := Point.vcInvFun_zero
      map_add' := Point.vcInvFun_add γ W.toAffine }

private theorem heq_vcHom (γ : VariableChange K) (W : WeierstrassCurve K) (hW : γ • W = W)
    (P : W.toAffine.Point) : HEq (Point.vcInvFun γ W.toAffine P) (vcHom γ W hW P) :=
  heq_castPt hW _

private theorem xy_vcHom (γ : VariableChange K) (W : WeierstrassCurve K) (hW : γ • W = W)
    (P : W.toAffine.Point) :
    xy (vcHom γ W hW P) = (xy P).map (fun q => (vcXInv γ q.1, vcYInv γ q.1 q.2)) := by
  show xy (castPt hW (Point.vcInvFun γ W.toAffine P)) = _
  rw [xy_castPt, xy_vcInvFun]

private theorem heq_of_xy_eq {W : WeierstrassCurve K} (γ : VariableChange K) (hW : γ • W = W)
    (T Q : W.toAffine.Point)
    (h : (xy T).map (fun q => (vcXInv γ q.1, vcYInv γ q.1 q.2)) = xy Q) :
    HEq (Point.vcInvFun γ W.toAffine T) Q := by
  have h1 : castPt hW (Point.vcInvFun γ W.toAffine T) = Q := by
    apply xy_injective
    rw [xy_castPt, xy_vcInvFun, h]
  exact (heq_castPt hW _).trans (h1 ▸ HEq.rfl)

end Transport

section Omega
variable (ω : Kˣ) (hω : (ω : K) ^ 2 + ω + 1 = 0)
include hω

private theorem omega_cube : (ω : K) ^ 3 = 1 := by
  linear_combination ((ω : K) - 1) * hω

private theorem omega_inv : ((ω⁻¹ : Kˣ) : K) = (ω : K) ^ 2 := by
  rw [Units.val_inv_eq_inv_val]
  exact inv_eq_of_mul_eq_one_right (by linear_combination omega_cube ω hω)

private theorem omega_inv_sq : ((ω⁻¹ : Kˣ) : K) ^ 2 = ω := by
  rw [omega_inv ω hω, ← pow_mul, show (2 * 2 : ℕ) = 3 + 1 by norm_num, pow_succ, omega_cube ω hω,
    one_mul]

private theorem omega_inv_cube : ((ω⁻¹ : Kˣ) : K) ^ 3 = 1 := by
  rw [omega_inv ω hω, ← pow_mul, show (2 * 3 : ℕ) = 3 * 2 by norm_num, pow_mul, omega_cube ω hω,
    one_pow]

private theorem omega_sq_cube : ((ω : K) ^ 2) ^ 3 = 1 := by
  rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, omega_cube ω hω, one_pow]

private theorem omega_sq_unit_inv : (((ω ^ 2)⁻¹ : Kˣ) : K) = ω := by
  rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  exact inv_eq_of_mul_eq_one_right (by linear_combination omega_cube ω hω)

private theorem omega_sq_inv_sq : (((ω ^ 2)⁻¹ : Kˣ) : K) ^ 2 = (ω : K) ^ 2 := by
  rw [omega_sq_unit_inv ω hω]

private theorem omega_sq_inv_cube : (((ω ^ 2)⁻¹ : Kˣ) : K) ^ 3 = 1 := by
  rw [omega_sq_unit_inv ω hω, omega_cube ω hω]

private theorem cube_cases (x : K) (hx : x ^ 3 = 1) : x = 1 ∨ x = ω ∨ x = (ω : K) ^ 2 := by
  have hmul : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination hx
  rcases mul_eq_zero.mp hmul with h | h
  · exact Or.inl (by linear_combination h)
  · have hmul' : (x - ω) * (x - (ω : K) ^ 2) = 0 := by
      linear_combination h + (-x + (ω : K) - 1) * hω
    rcases mul_eq_zero.mp hmul' with h' | h'
    · exact Or.inr (Or.inl (by linear_combination h'))
    · exact Or.inr (Or.inr (by linear_combination h'))

private theorem u_cases (u : Kˣ) (hu : (u : K) ^ 3 = 1) :
    (u : K) = 1 ∨ (u : K) = ω ∨ (u : K) = (ω : K) ^ 2 := by
  exact cube_cases ω hω _ hu

private theorem s_cases (s : K) (hs : s ^ 4 = s) :
    s = 0 ∨ s = 1 ∨ s = ω ∨ s = (ω : K) ^ 2 := by
  have hmul : s * (s ^ 3 - 1) = 0 := by linear_combination hs
  rcases mul_eq_zero.mp hmul with h | h
  · exact Or.inl h
  · exact Or.inr (cube_cases ω hω s (by linear_combination h))

end Omega

private abbrev E (K : Type*) [Field K] : WeierstrassCurve K := ⟨0, 0, 1, 0, 0⟩

section NormalForms
variable [DecidableEq K]

private def NormalForm (u : Kˣ) (s t : K) (m : (E K).toAffine.Point →+ (E K).toAffine.Point) :
    Prop :=
  ∀ P, xy (m P) = (xy P).map fun q =>
    (((u⁻¹ : Kˣ) : K) ^ 2 * (q.1 - s ^ 2), ((u⁻¹ : Kˣ) : K) ^ 3 * (q.2 - t - s * (q.1 - s ^ 2)))

private theorem heq_pos {u : Kˣ} {s t : K} {m : (E K).toAffine.Point →+ (E K).toAffine.Point}
    (hm : NormalForm u s t m) (hst : (⟨u, s ^ 2, s, t⟩ : VariableChange K) • E K = E K)
    (T : (E K).toAffine.Point) :
    HEq (Point.vcInvFun (⟨u, s ^ 2, s, t⟩ : VariableChange K) (E K).toAffine T) (m T) := by
  apply heq_of_xy_eq _ hst
  rw [hm T]
  rcases T with _ | ⟨x, y, h⟩
  · rfl
  · simp [xy, vcXInv, vcYInv]

private theorem normalForm_id : NormalForm (1 : Kˣ) (0 : K) 0 (AddMonoidHom.id _) := by
  intro P
  simp only [AddMonoidHom.id_apply]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq,
      inv_one, Units.val_one, one_pow, one_mul]
    constructor
    · linear_combination
    · linear_combination

end NormalForms

section CharTwoCurve
variable [CharP K 2]

private theorem two_eq_zero : (2 : K) = 0 := by simpa using CharP.cast_eq_zero K 2

private theorem stab_iff (γ : VariableChange K) :
    γ • E K = E K ↔
      (γ.u : K) ^ 3 = 1 ∧ γ.r = γ.s ^ 2 ∧ γ.s ^ 4 = γ.s ∧ γ.t ^ 2 + γ.t = γ.s ^ 6 := by
  have h2 : (2 : K) = 0 := two_eq_zero
  have hui : ((γ.u⁻¹ : Kˣ) : K) = (γ.u : K)⁻¹ := Units.val_inv_eq_inv_val _
  have hui0 : ((γ.u⁻¹ : Kˣ) : K) ≠ 0 := (γ.u⁻¹).ne_zero
  have hu3_of : ((γ.u⁻¹ : Kˣ) : K) ^ 3 = 1 → (γ.u : K) ^ 3 = 1 := by
    intro h
    rw [hui, inv_pow, inv_eq_one] at h
    exact h
  constructor
  · intro h
    have h2' := congrArg WeierstrassCurve.a₂ h
    have h3' := congrArg WeierstrassCurve.a₃ h
    have h4' := congrArg WeierstrassCurve.a₄ h
    have h6' := congrArg WeierstrassCurve.a₆ h
    simp only [variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆, E]
      at h2' h3' h4' h6'

    have hu : (γ.u : K) ^ 3 = 1 := by
      apply hu3_of
      linear_combination h3' - ((γ.u⁻¹ : Kˣ) : K) ^ 3 * γ.t * h2

    have hr : γ.r = γ.s ^ 2 := by
      have hmul : ((γ.u⁻¹ : Kˣ) : K) ^ 2 * (3 * γ.r - γ.s ^ 2) = 0 := by linear_combination h2'
      rcases mul_eq_zero.mp hmul with h0 | h0
      · exact absurd h0 (pow_ne_zero _ hui0)
      · linear_combination h0 - γ.r * h2

    have hs : γ.s ^ 4 = γ.s := by
      have hmul : ((γ.u⁻¹ : Kˣ) : K) ^ 4 * (-γ.s + 3 * γ.r ^ 2 - 2 * γ.s * γ.t) = 0 := by
        linear_combination h4'
      rcases mul_eq_zero.mp hmul with h0 | h0
      · exact absurd h0 (pow_ne_zero _ hui0)
      · rw [hr] at h0
        linear_combination h0 - (γ.s ^ 4 - γ.s * γ.t) * h2

    have ht : γ.t ^ 2 + γ.t = γ.s ^ 6 := by
      have hmul : ((γ.u⁻¹ : Kˣ) : K) ^ 6 * (γ.r ^ 3 - γ.t - γ.t ^ 2) = 0 := by
        linear_combination h6'
      rcases mul_eq_zero.mp hmul with h0 | h0
      · exact absurd h0 (pow_ne_zero _ hui0)
      · rw [hr] at h0
        linear_combination -h0
    exact ⟨hu, hr, hs, ht⟩
  · rintro ⟨hu, hr, hs, ht⟩
    have hui3 : ((γ.u⁻¹ : Kˣ) : K) ^ 3 = 1 := by rw [hui, inv_pow, hu, inv_one]
    have hui6 : ((γ.u⁻¹ : Kˣ) : K) ^ 6 = 1 := by
      rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, hui3, one_pow]
    have hui4 : ((γ.u⁻¹ : Kˣ) : K) ^ 4 = (γ.u⁻¹ : Kˣ) := by
      rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hui3, one_mul]
    ext
    · simp only [variableChange_a₁, E]
      linear_combination ((γ.u⁻¹ : Kˣ) : K) * γ.s * h2
    · simp only [variableChange_a₂, E]
      rw [hr]
      linear_combination ((γ.u⁻¹ : Kˣ) : K) ^ 2 * γ.s ^ 2 * h2
    · simp only [variableChange_a₃, E]
      linear_combination hui3 + ((γ.u⁻¹ : Kˣ) : K) ^ 3 * γ.t * h2
    · simp only [variableChange_a₄, E]
      rw [hr, hui4]
      linear_combination ((γ.u⁻¹ : Kˣ) : K) * (hs + (γ.s ^ 4 - γ.s * γ.t) * h2)
    · simp only [variableChange_a₆, E]
      rw [hr, hui6]
      linear_combination -ht

private theorem mk_stab (u : Kˣ) (hu : (u : K) ^ 3 = 1) (s t : K) (hs : s ^ 4 = s)
    (ht : t ^ 2 + t = s ^ 6) : (⟨u, s ^ 2, s, t⟩ : VariableChange K) • E K = E K :=
  (stab_iff _).mpr ⟨hu, rfl, hs, ht⟩

private theorem t_cases (t t₀ c : K) (ht : t ^ 2 + t = c) (ht₀ : t₀ ^ 2 + t₀ = c) :
    t = t₀ ∨ t = t₀ + 1 := by
  have h2 : (2 : K) = 0 := two_eq_zero
  have hmul : (t - t₀) * (t + t₀ + 1) = 0 := by linear_combination ht - ht₀
  rcases mul_eq_zero.mp hmul with h | h
  · exact Or.inl (by linear_combination h)
  · exact Or.inr (by linear_combination h - (t₀ + 1) * h2)

private theorem xy_neg' (P : (E K).toAffine.Point) :
    xy (-P) = (xy P).map fun q => (q.1, q.2 + 1) := by
  rw [xy_neg]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · have h2 : (2 : K) = 0 := two_eq_zero
    simp only [Option.map_some, Affine.negY, Option.some.injEq, Prod.mk.injEq, true_and]
    linear_combination (-y - 1) * h2

section CurveOmega
variable (ω : Kˣ) (hω : (ω : K) ^ 2 + ω + 1 = 0)
include hω

private theorem omega_sq : (ω : K) ^ 2 = ω + 1 := by
  linear_combination hω + (-(ω : K) - 1) * two_eq_zero (K := K)

private theorem omega_sol : (ω : K) ^ 2 + ω = 1 := by
  linear_combination hω - two_eq_zero (K := K)

private theorem sigma_stab : (⟨ω, 0, 0, 0⟩ : VariableChange K) • E K = E K :=
  (stab_iff _).mpr ⟨omega_cube ω hω, by simp, by simp, by norm_num⟩

private theorem i_stab : (⟨1, 1, 1, (ω : K)⟩ : VariableChange K) • E K = E K :=
  (stab_iff _).mpr ⟨by simp, by simp, by simp, by
    show (ω : K) ^ 2 + ω = (1 : K) ^ 6
    rw [omega_sol ω hω, one_pow]⟩

private theorem j_stab : (⟨1, ω, (ω : K) ^ 2, ω⟩ : VariableChange K) • E K = E K :=
  (stab_iff _).mpr ⟨by simp, by
    show (ω : K) = ((ω : K) ^ 2) ^ 2
    rw [← pow_mul, show (2 * 2 : ℕ) = 3 + 1 by norm_num, pow_succ, omega_cube ω hω, one_mul], by
    show ((ω : K) ^ 2) ^ 4 = (ω : K) ^ 2
    rw [← pow_mul, show (2 * 4 : ℕ) = 3 * 2 + 2 by norm_num, pow_add, pow_mul, omega_cube ω hω,
      one_pow, one_mul], by
    show (ω : K) ^ 2 + ω = ((ω : K) ^ 2) ^ 6
    rw [omega_sol ω hω, ← pow_mul, show (2 * 6 : ℕ) = 3 * 4 by norm_num, pow_mul, omega_cube ω hω,
      one_pow]⟩

end CurveOmega

end CharTwoCurve

section CharTwoPoints
variable [DecidableEq K] [CharP K 2]

private theorem heq_neg {u : Kˣ} (hu : (u : K) ^ 3 = 1) {s t : K}
    {m : (E K).toAffine.Point →+ (E K).toAffine.Point} (hm : NormalForm u s t m)
    (hst : (⟨u, s ^ 2, s, t + 1⟩ : VariableChange K) • E K = E K) (T : (E K).toAffine.Point) :
    HEq (Point.vcInvFun (⟨u, s ^ 2, s, t + 1⟩ : VariableChange K) (E K).toAffine T) (-(m T)) := by
  have h2 : (2 : K) = 0 := two_eq_zero
  have hui3 : ((u⁻¹ : Kˣ) : K) ^ 3 = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, hu, inv_one]
  apply heq_of_xy_eq _ hst
  rw [xy_neg, hm T]
  rcases T with _ | ⟨x, y, h⟩
  · rfl
  · simp only [xy, Option.map_some, vcXInv, vcYInv, Affine.negY, Option.some.injEq,
      Prod.mk.injEq, true_and]
    linear_combination -hui3 + ((u⁻¹ : Kˣ) : K) ^ 3 * (y - t - s * (x - s ^ 2)) * h2

private theorem stab_case (γ : VariableChange K) (hγ : γ • E K = E K) (u : Kˣ) (s t : K)
    (m : (E K).toAffine.Point →+ (E K).toAffine.Point) (hm : NormalForm u s t m)
    (hu : γ.u = u) (hs : γ.s = s) (ht : γ.t = t ∨ γ.t = t + 1) :
    (∀ T, HEq (Point.vcInvFun γ (E K).toAffine T) (m T)) ∨
      (∀ T, HEq (Point.vcInvFun γ (E K).toAffine T) (-(m T))) := by
  obtain ⟨hu3, hr, -, -⟩ := (stab_iff γ).mp hγ
  obtain ⟨u', r, s', t'⟩ := γ
  simp only at hu hs ht hr hu3
  subst hu hs hr
  rcases ht with ht | ht
  · subst ht
    exact Or.inl (heq_pos hm hγ)
  · subst ht
    exact Or.inr (heq_neg hu3 hm hγ)

section PointsOmega
variable (ω : Kˣ) (hω : (ω : K) ^ 2 + ω + 1 = 0)
include hω

private noncomputable def σH : (E K).toAffine.Point →+ (E K).toAffine.Point :=
  vcHom _ (E K) (sigma_stab ω hω)

private noncomputable def iH : (E K).toAffine.Point →+ (E K).toAffine.Point :=
  vcHom _ (E K) (i_stab ω hω)

private noncomputable def jH : (E K).toAffine.Point →+ (E K).toAffine.Point :=
  vcHom _ (E K) (j_stab ω hω)

private theorem xy_σ (P : (E K).toAffine.Point) :
    xy (σH ω hω P) = (xy P).map fun q => ((ω : K) * q.1, q.2) := by
  rw [σH, xy_vcHom]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, vcXInv, vcYInv, omega_inv_sq ω hω, omega_inv_cube ω hω,
      Option.some.injEq, Prod.mk.injEq]
    constructor <;> ring

private theorem xy_i (P : (E K).toAffine.Point) :
    xy (iH ω hω P) = (xy P).map fun q => (q.1 + 1, q.2 + q.1 + (ω : K) ^ 2) := by
  have h2 : (2 : K) = 0 := two_eq_zero
  rw [iH, xy_vcHom]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, vcXInv, vcYInv, inv_one, Units.val_one, one_pow, one_mul,
      Option.some.injEq, Prod.mk.injEq]
    constructor
    · linear_combination -h2
    · linear_combination -hω + (1 - x) * h2

private theorem xy_j (P : (E K).toAffine.Point) :
    xy (jH ω hω P) =
      (xy P).map fun q => (q.1 + (ω : K), q.2 + (ω : K) ^ 2 * q.1 + (ω : K) ^ 2) := by
  have h2 : (2 : K) = 0 := two_eq_zero
  rw [jH, xy_vcHom]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, vcXInv, vcYInv, inv_one, Units.val_one, one_pow, one_mul,
      Option.some.injEq, Prod.mk.injEq]
    constructor
    · linear_combination -(ω : K) * h2
    · linear_combination (ω : K) * hω + (-(ω : K) ^ 2 - ω - (ω : K) ^ 2 * x) * h2

private theorem σσσ (T : (E K).toAffine.Point) : σH ω hω (σH ω hω (σH ω hω T)) = T := by
  apply xy_injective
  rw [xy_σ, xy_σ, xy_σ]
  rcases xy T with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    linear_combination x * omega_cube ω hω

private theorem ii (T : (E K).toAffine.Point) : iH ω hω (iH ω hω T) = -T := by
  have h2 : (2 : K) = 0 := two_eq_zero
  apply xy_injective
  rw [xy_i, xy_i, xy_neg']
  rcases xy T with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    exact ⟨by linear_combination h2, by linear_combination (x + (ω : K) ^ 2) * h2⟩

private theorem jj (T : (E K).toAffine.Point) : jH ω hω (jH ω hω T) = -T := by
  have h2 : (2 : K) = 0 := two_eq_zero
  apply xy_injective
  rw [xy_j, xy_j, xy_neg']
  rcases xy T with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    exact ⟨by linear_combination (ω : K) * h2,
      by linear_combination ((ω : K) ^ 2 * x + (ω : K) ^ 2) * h2 + ((ω : K) - 1) * hω⟩

private theorem ij_eq_neg_ji (T : (E K).toAffine.Point) :
    iH ω hω (jH ω hω T) = -(jH ω hω (iH ω hω T)) := by
  have h2 : (2 : K) = 0 := two_eq_zero
  apply xy_injective
  rw [xy_i, xy_j, xy_neg', xy_j, xy_i]
  rcases xy T with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    exact ⟨by linear_combination, by linear_combination -hω + (ω : K) * h2⟩

private theorem σi_eq_jσ (T : (E K).toAffine.Point) :
    σH ω hω (iH ω hω T) = jH ω hω (σH ω hω T) := by
  apply xy_injective
  rw [xy_σ, xy_i, xy_j, xy_σ]
  rcases xy T with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    exact ⟨by linear_combination, by linear_combination -x * omega_cube ω hω⟩

private theorem σj_eq_jiσ (T : (E K).toAffine.Point) :
    σH ω hω (jH ω hω T) = jH ω hω (iH ω hω (σH ω hω T)) := by
  have h2 : (2 : K) = 0 := two_eq_zero
  apply xy_injective
  rw [xy_σ, xy_j, xy_j, xy_i, xy_σ]
  rcases xy T with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    exact ⟨by linear_combination hω - ((ω : K) + 1) * h2,
      by linear_combination x * hω - x * omega_cube ω hω + (-(ω : K) * x - (ω : K) ^ 2 - x) * h2⟩

private theorem normalForm_σ : NormalForm ω (0 : K) 0 (σH ω hω) := by
  intro P
  rw [xy_σ ω hω]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq,
      omega_inv_sq ω hω, omega_inv_cube ω hω, one_mul]
    constructor
    · linear_combination
    · linear_combination

private theorem normalForm_σσ : NormalForm (ω ^ 2) (0 : K) 0 ((σH ω hω).comp (σH ω hω)) := by
  intro P
  simp only [AddMonoidHom.comp_apply]
  rw [xy_σ ω hω, xy_σ ω hω]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq,
      omega_sq_inv_sq ω hω, omega_sq_inv_cube ω hω, one_mul]
    constructor
    · linear_combination
    · linear_combination

private theorem normalForm_i : NormalForm (1 : Kˣ) (1 : K) ω (iH ω hω) := by
  intro P
  have h2 : (2 : K) = 0 := two_eq_zero
  rw [xy_i ω hω]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq,
      inv_one, Units.val_one, one_pow, one_mul]
    constructor
    · linear_combination h2
    · linear_combination hω + (x - 1) * h2

private theorem normalForm_iσ : NormalForm ω (ω : K) ω ((iH ω hω).comp (σH ω hω)) := by
  intro P
  have h2 : (2 : K) = 0 := two_eq_zero
  simp only [AddMonoidHom.comp_apply]
  rw [xy_i ω hω, xy_σ ω hω]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq,
      omega_inv_sq ω hω, omega_inv_cube ω hω, one_mul]
    constructor
    · linear_combination omega_cube ω hω + h2
    · linear_combination hω - omega_cube ω hω + ((ω : K) * x - 1) * h2

private theorem normalForm_iσσ :
    NormalForm (ω ^ 2) ((ω : K) ^ 2) ω ((iH ω hω).comp ((σH ω hω).comp (σH ω hω))) := by
  intro P
  have h2 : (2 : K) = 0 := two_eq_zero
  simp only [AddMonoidHom.comp_apply]
  rw [xy_i ω hω, xy_σ ω hω, xy_σ ω hω]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq,
      omega_sq_inv_sq ω hω, omega_sq_inv_cube ω hω, one_mul]
    constructor
    · linear_combination ((ω : K) ^ 3 + 1) * omega_cube ω hω + h2
    · linear_combination hω - ((ω : K) ^ 3 + 1) * omega_cube ω hω + ((ω : K) ^ 2 * x - 1) * h2

private theorem normalForm_j : NormalForm (1 : Kˣ) ((ω : K) ^ 2) ω (jH ω hω) := by
  intro P
  have h2 : (2 : K) = 0 := two_eq_zero
  rw [xy_j ω hω]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq,
      inv_one, Units.val_one, one_pow, one_mul]
    constructor
    · linear_combination (ω : K) * omega_cube ω hω + (ω : K) * h2
    · linear_combination hω - ((ω : K) ^ 3 + 1) * omega_cube ω hω + ((ω : K) ^ 2 * x - 1) * h2

private theorem normalForm_jσ : NormalForm ω (1 : K) ω ((jH ω hω).comp (σH ω hω)) := by
  intro P
  have h2 : (2 : K) = 0 := two_eq_zero
  simp only [AddMonoidHom.comp_apply]
  rw [xy_j ω hω, xy_σ ω hω]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq,
      omega_inv_sq ω hω, omega_inv_cube ω hω, one_mul]
    constructor
    · linear_combination (ω : K) * h2
    · linear_combination hω + x * omega_cube ω hω + (x - 1) * h2

private theorem normalForm_jσσ :
    NormalForm (ω ^ 2) (ω : K) ω ((jH ω hω).comp ((σH ω hω).comp (σH ω hω))) := by
  intro P
  have h2 : (2 : K) = 0 := two_eq_zero
  simp only [AddMonoidHom.comp_apply]
  rw [xy_j ω hω, xy_σ ω hω, xy_σ ω hω]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq,
      omega_sq_inv_sq ω hω, omega_sq_inv_cube ω hω, one_mul]
    constructor
    · linear_combination (ω : K) * omega_cube ω hω + (ω : K) * h2
    · linear_combination hω + ((ω : K) * x - 1) * omega_cube ω hω + ((ω : K) * x - 1) * h2

private theorem normalForm_ij :
    NormalForm (1 : Kˣ) (ω : K) ((ω : K) ^ 2) ((iH ω hω).comp (jH ω hω)) := by
  intro P
  have h2 : (2 : K) = 0 := two_eq_zero
  simp only [AddMonoidHom.comp_apply]
  rw [xy_i ω hω, xy_j ω hω]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq,
      inv_one, Units.val_one, one_pow, one_mul]
    constructor
    · linear_combination hω
    · linear_combination (x + 1) * hω - omega_cube ω hω + ((ω : K) ^ 2 - 1) * h2

private theorem normalForm_ijσ :
    NormalForm ω ((ω : K) ^ 2) ((ω : K) ^ 2) (((iH ω hω).comp (jH ω hω)).comp (σH ω hω)) := by
  intro P
  have h2 : (2 : K) = 0 := two_eq_zero
  simp only [AddMonoidHom.comp_apply]
  rw [xy_i ω hω, xy_j ω hω, xy_σ ω hω]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq,
      omega_inv_sq ω hω, omega_inv_cube ω hω, one_mul]
    constructor
    · linear_combination hω + (ω : K) ^ 2 * omega_cube ω hω
    · linear_combination (x + 1) * hω + (x - ((ω : K) ^ 3 + 1)) * omega_cube ω hω +
        ((ω : K) ^ 2 - 1) * h2

private theorem normalForm_ijσσ :
    NormalForm (ω ^ 2) (1 : K) ((ω : K) ^ 2)
      (((iH ω hω).comp (jH ω hω)).comp ((σH ω hω).comp (σH ω hω))) := by
  intro P
  have h2 : (2 : K) = 0 := two_eq_zero
  simp only [AddMonoidHom.comp_apply]
  rw [xy_i ω hω, xy_j ω hω, xy_σ ω hω, xy_σ ω hω]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq,
      omega_sq_inv_sq ω hω, omega_sq_inv_cube ω hω, one_mul]
    constructor
    · linear_combination hω
    · linear_combination (x + 1) * hω + (ω : K) * x * omega_cube ω hω + ((ω : K) ^ 2 - 1) * h2

private theorem forall_stab (γ : VariableChange K) (hγ : γ • E K = E K) :
    ∃ m : (E K).toAffine.Point →+ (E K).toAffine.Point,
      (m = AddMonoidHom.id _ ∨ m = σH ω hω ∨ m = (σH ω hω).comp (σH ω hω) ∨
          m = iH ω hω ∨ m = (iH ω hω).comp (σH ω hω) ∨
          m = (iH ω hω).comp ((σH ω hω).comp (σH ω hω)) ∨
          m = jH ω hω ∨ m = (jH ω hω).comp (σH ω hω) ∨
          m = (jH ω hω).comp ((σH ω hω).comp (σH ω hω)) ∨
          m = (iH ω hω).comp (jH ω hω) ∨ m = ((iH ω hω).comp (jH ω hω)).comp (σH ω hω) ∨
          m = ((iH ω hω).comp (jH ω hω)).comp ((σH ω hω).comp (σH ω hω))) ∧
      ((∀ T, HEq (Point.vcInvFun γ (E K).toAffine T) (m T)) ∨
        (∀ T, HEq (Point.vcInvFun γ (E K).toAffine T) (-(m T)))) := by
  obtain ⟨hu, -, hs, ht⟩ := (stab_iff γ).mp hγ
  have h2 : (2 : K) = 0 := two_eq_zero
  rcases u_cases ω hω γ.u hu with hu1 | hu1 | hu1 <;>
    rcases s_cases ω hω γ.s hs with hs1 | hs1 | hs1 | hs1
  · rw [hs1] at ht
    refine ⟨AddMonoidHom.id _,
      Or.inl rfl, ?_⟩
    refine stab_case γ hγ _ _ _ _ (normalForm_id) ?_ hs1 (t_cases _ (0 : K) _ ht ?_)
    · exact Units.val_eq_one.mp hu1
    · norm_num
  · rw [hs1] at ht
    refine ⟨iH ω hω,
      Or.inr (Or.inr (Or.inr (Or.inl rfl))), ?_⟩
    refine stab_case γ hγ _ _ _ _ (normalForm_i ω hω) ?_ hs1 (t_cases _ (ω : K) _ ht ?_)
    · exact Units.val_eq_one.mp hu1
    · rw [omega_sol ω hω, one_pow]
  · rw [hs1] at ht
    refine ⟨(iH ω hω).comp (jH ω hω),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl rfl))))))))), ?_⟩
    refine stab_case γ hγ _ _ _ _ (normalForm_ij ω hω) ?_ hs1 (t_cases _ ((ω : K) ^ 2) _ ht ?_)
    · exact Units.val_eq_one.mp hu1
    · linear_combination ((ω : K) - ((ω : K) ^ 3 + 1)) * omega_cube ω hω + hω - h2
  · rw [hs1] at ht
    refine ⟨jH ω hω,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))), ?_⟩
    refine stab_case γ hγ _ _ _ _ (normalForm_j ω hω) ?_ hs1 (t_cases _ (ω : K) _ ht ?_)
    · exact Units.val_eq_one.mp hu1
    · linear_combination hω - ((ω : K) ^ 9 + (ω : K) ^ 6 + (ω : K) ^ 3 + 1) * omega_cube ω hω - h2
  · rw [hs1] at ht
    refine ⟨σH ω hω,
      Or.inr (Or.inl rfl), ?_⟩
    refine stab_case γ hγ _ _ _ _ (normalForm_σ ω hω) ?_ hs1 (t_cases _ (0 : K) _ ht ?_)
    · exact Units.ext hu1
    · norm_num
  · rw [hs1] at ht
    refine ⟨(jH ω hω).comp (σH ω hω),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))), ?_⟩
    refine stab_case γ hγ _ _ _ _ (normalForm_jσ ω hω) ?_ hs1 (t_cases _ (ω : K) _ ht ?_)
    · exact Units.ext hu1
    · rw [omega_sol ω hω, one_pow]
  · rw [hs1] at ht
    refine ⟨(iH ω hω).comp (σH ω hω),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), ?_⟩
    refine stab_case γ hγ _ _ _ _ (normalForm_iσ ω hω) ?_ hs1 (t_cases _ (ω : K) _ ht ?_)
    · exact Units.ext hu1
    · linear_combination hω - ((ω : K) ^ 3 + 1) * omega_cube ω hω - h2
  · rw [hs1] at ht
    refine ⟨((iH ω hω).comp (jH ω hω)).comp (σH ω hω),
      Or.inr (Or.inr (Or.inr (Or.inr (
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))), ?_⟩
    refine stab_case γ hγ _ _ _ _ (normalForm_ijσ ω hω) ?_ hs1
        (t_cases _ ((ω : K) ^ 2) _ ht ?_)
    · exact Units.ext hu1
    · linear_combination ((ω : K) - ((ω : K) ^ 9 + (ω : K) ^ 6 + (ω : K) ^ 3 +
        1)) * omega_cube ω hω + hω - h2
  · rw [hs1] at ht
    refine ⟨(σH ω hω).comp (σH ω hω),
      Or.inr (Or.inr (Or.inl rfl)), ?_⟩
    refine stab_case γ hγ _ _ _ _ (normalForm_σσ ω hω) ?_ hs1 (t_cases _ (0 : K) _ ht ?_)
    · exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hu1)
    · norm_num
  · rw [hs1] at ht
    refine ⟨((iH ω hω).comp (jH ω hω)).comp ((σH ω hω).comp (σH ω hω)),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr rfl)))))))))), ?_⟩
    refine stab_case γ hγ _ _ _ _ (normalForm_ijσσ ω hω) ?_ hs1
        (t_cases _ ((ω : K) ^ 2) _ ht ?_)
    · exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hu1)
    · linear_combination (ω : K) * omega_cube ω hω + hω - h2
  · rw [hs1] at ht
    refine ⟨(jH ω hω).comp ((σH ω hω).comp (σH ω hω)),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))), ?_⟩
    refine stab_case γ hγ _ _ _ _ (normalForm_jσσ ω hω) ?_ hs1 (t_cases _ (ω : K) _ ht ?_)
    · exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hu1)
    · linear_combination hω - ((ω : K) ^ 3 + 1) * omega_cube ω hω - h2
  · rw [hs1] at ht
    refine ⟨(iH ω hω).comp ((σH ω hω).comp (σH ω hω)),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), ?_⟩
    refine stab_case γ hγ _ _ _ _ (normalForm_iσσ ω hω) ?_ hs1 (t_cases _ (ω : K) _ ht ?_)
    · exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hu1)
    · linear_combination hω - ((ω : K) ^ 9 + (ω : K) ^ 6 + (ω : K) ^ 3 + 1) * omega_cube ω hω - h2

private theorem forall_twelve (m : (E K).toAffine.Point →+ (E K).toAffine.Point)
    (hm : m = AddMonoidHom.id _ ∨ m = σH ω hω ∨ m = (σH ω hω).comp (σH ω hω) ∨
        m = iH ω hω ∨ m = (iH ω hω).comp (σH ω hω) ∨
        m = (iH ω hω).comp ((σH ω hω).comp (σH ω hω)) ∨
        m = jH ω hω ∨ m = (jH ω hω).comp (σH ω hω) ∨
        m = (jH ω hω).comp ((σH ω hω).comp (σH ω hω)) ∨
        m = (iH ω hω).comp (jH ω hω) ∨ m = ((iH ω hω).comp (jH ω hω)).comp (σH ω hω) ∨
        m = ((iH ω hω).comp (jH ω hω)).comp ((σH ω hω).comp (σH ω hω))) :
    ∃ γ : VariableChange K, γ • E K = E K ∧
      ∀ T, HEq (Point.vcInvFun γ (E K).toAffine T) (m T) := by
  have h2 : (2 : K) = 0 := two_eq_zero
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hst :
        (⟨(1 : Kˣ), (0 : K) ^ 2, (0 : K), (0 : K)⟩ : VariableChange K) • E K = E K := by
      refine mk_stab _ ?_ _ _ ?_ ?_
      · simp
      · norm_num
      · norm_num
    exact ⟨_, hst, fun T => heq_pos (normalForm_id) hst T⟩
  · have hst :
        (⟨ω, (0 : K) ^ 2, (0 : K), (0 : K)⟩ : VariableChange K) • E K = E K := by
      refine mk_stab _ ?_ _ _ ?_ ?_
      · exact omega_cube ω hω
      · norm_num
      · norm_num
    exact ⟨_, hst, fun T => heq_pos (normalForm_σ ω hω) hst T⟩
  · have hst :
        (⟨(ω ^ 2 : Kˣ), (0 : K) ^ 2, (0 : K), (0 : K)⟩ : VariableChange K) • E K = E K := by
      refine mk_stab _ ?_ _ _ ?_ ?_
      · rw [Units.val_pow_eq_pow_val]; exact omega_sq_cube ω hω
      · norm_num
      · norm_num
    exact ⟨_, hst, fun T => heq_pos (normalForm_σσ ω hω) hst T⟩
  · have hst :
        (⟨(1 : Kˣ), (1 : K) ^ 2, (1 : K), (ω : K)⟩ : VariableChange K) • E K = E K := by
      refine mk_stab _ ?_ _ _ ?_ ?_
      · simp
      · norm_num
      · rw [omega_sol ω hω, one_pow]
    exact ⟨_, hst, fun T => heq_pos (normalForm_i ω hω) hst T⟩
  · have hst :
        (⟨ω, (ω : K) ^ 2, (ω : K), (ω : K)⟩ : VariableChange K) • E K = E K := by
      refine mk_stab _ ?_ _ _ ?_ ?_
      · exact omega_cube ω hω
      · linear_combination (ω : K) * omega_cube ω hω
      · linear_combination hω - ((ω : K) ^ 3 + 1) * omega_cube ω hω - h2
    exact ⟨_, hst, fun T => heq_pos (normalForm_iσ ω hω) hst T⟩
  · have hst :
        (⟨(ω ^ 2 : Kˣ), ((ω : K) ^ 2) ^ 2, ((ω : K) ^ 2), (ω : K)⟩
            : VariableChange K) • E K = E K := by
      refine mk_stab _ ?_ _ _ ?_ ?_
      · rw [Units.val_pow_eq_pow_val]; exact omega_sq_cube ω hω
      · linear_combination (ω : K) ^ 2 * ((ω : K) ^ 3 + 1) * omega_cube ω hω
      · linear_combination hω - ((ω : K) ^ 9 + (ω : K) ^ 6 + (ω : K) ^ 3 + 1) * omega_cube ω hω - h2
    exact ⟨_, hst, fun T => heq_pos (normalForm_iσσ ω hω) hst T⟩
  · have hst :
        (⟨(1 : Kˣ), ((ω : K) ^ 2) ^ 2, ((ω : K) ^ 2), (ω : K)⟩ : VariableChange K) • E K = E K := by
      refine mk_stab _ ?_ _ _ ?_ ?_
      · simp
      · linear_combination (ω : K) ^ 2 * ((ω : K) ^ 3 + 1) * omega_cube ω hω
      · linear_combination hω - ((ω : K) ^ 9 + (ω : K) ^ 6 + (ω : K) ^ 3 + 1) * omega_cube ω hω - h2
    exact ⟨_, hst, fun T => heq_pos (normalForm_j ω hω) hst T⟩
  · have hst :
        (⟨ω, (1 : K) ^ 2, (1 : K), (ω : K)⟩ : VariableChange K) • E K = E K := by
      refine mk_stab _ ?_ _ _ ?_ ?_
      · exact omega_cube ω hω
      · norm_num
      · rw [omega_sol ω hω, one_pow]
    exact ⟨_, hst, fun T => heq_pos (normalForm_jσ ω hω) hst T⟩
  · have hst :
        (⟨(ω ^ 2 : Kˣ), (ω : K) ^ 2, (ω : K), (ω : K)⟩ : VariableChange K) • E K = E K := by
      refine mk_stab _ ?_ _ _ ?_ ?_
      · rw [Units.val_pow_eq_pow_val]; exact omega_sq_cube ω hω
      · linear_combination (ω : K) * omega_cube ω hω
      · linear_combination hω - ((ω : K) ^ 3 + 1) * omega_cube ω hω - h2
    exact ⟨_, hst, fun T => heq_pos (normalForm_jσσ ω hω) hst T⟩
  · have hst :
        (⟨(1 : Kˣ), (ω : K) ^ 2, (ω : K), ((ω : K) ^ 2)⟩ : VariableChange K) • E K = E K := by
      refine mk_stab _ ?_ _ _ ?_ ?_
      · simp
      · linear_combination (ω : K) * omega_cube ω hω
      · linear_combination ((ω : K) - ((ω : K) ^ 3 + 1)) * omega_cube ω hω + hω - h2
    exact ⟨_, hst, fun T => heq_pos (normalForm_ij ω hω) hst T⟩
  · have hst :
        (⟨ω, ((ω : K) ^ 2) ^ 2, ((ω : K) ^ 2), ((ω : K) ^ 2)⟩ : VariableChange K) • E K = E K := by
      refine mk_stab _ ?_ _ _ ?_ ?_
      · exact omega_cube ω hω
      · linear_combination (ω : K) ^ 2 * ((ω : K) ^ 3 + 1) * omega_cube ω hω
      · linear_combination ((ω : K) - ((ω : K) ^ 9 + (ω : K) ^ 6 + (ω : K) ^ 3 +
          1)) * omega_cube ω hω + hω - h2
    exact ⟨_, hst, fun T => heq_pos (normalForm_ijσ ω hω) hst T⟩
  · have hst :
        (⟨(ω ^ 2 : Kˣ), (1 : K) ^ 2, (1 : K), ((ω : K) ^ 2)⟩ : VariableChange K) • E K = E K := by
      refine mk_stab _ ?_ _ _ ?_ ?_
      · rw [Units.val_pow_eq_pow_val]; exact omega_sq_cube ω hω
      · norm_num
      · linear_combination (ω : K) * omega_cube ω hω + hω - h2
    exact ⟨_, hst, fun T => heq_pos (normalForm_ijσσ ω hω) hst T⟩

end PointsOmega

end CharTwoPoints

end AutCurveCharTwo

open AutCurveCharTwo in
theorem solution
    {K : Type*} [Field K] [DecidableEq K] [CharP K 2] (ω : Kˣ)
    (hω : (ω : K) ^ 2 + ω + 1 = 0) :
    ∃ σ i j : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine.Point →+
        (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine.Point,
      (∀ T, HEq (Point.vcInvFun (⟨ω, 0, 0, 0⟩ : VariableChange K)
          (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine T) (σ T)) ∧
      (∀ T, HEq (Point.vcInvFun (⟨1, 1, 1, ω⟩ : VariableChange K)
          (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine T) (i T)) ∧
      (∀ T, HEq (Point.vcInvFun (⟨1, ω, (ω : K) ^ 2, ω⟩ : VariableChange K)
          (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine T) (j T)) ∧
      (∀ T, σ (σ (σ T)) = T) ∧ (∀ T, i (i T) = -T) ∧ (∀ T, j (j T) = -T) ∧
      (∀ T, i (j T) = -(j (i T))) ∧ (∀ T, σ (i T) = j (σ T)) ∧
      (∀ T, σ (j T) = j (i (σ T))) ∧
      (∀ γ : VariableChange K,
          γ • (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K) = ⟨0, 0, 1, 0, 0⟩ →
        ∃ m : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine.Point →+
            (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine.Point,
          (m = AddMonoidHom.id _ ∨ m = σ ∨ m = σ.comp σ ∨
              m = i ∨ m = i.comp σ ∨ m = i.comp (σ.comp σ) ∨
              m = j ∨ m = j.comp σ ∨ m = j.comp (σ.comp σ) ∨
              m = i.comp j ∨ m = (i.comp j).comp σ ∨ m = (i.comp j).comp (σ.comp σ)) ∧
          ((∀ T, HEq (Point.vcInvFun γ (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine T) (m T)) ∨
            (∀ T, HEq (Point.vcInvFun γ (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine T)
              (-(m T))))) ∧
      (∀ m : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine.Point →+
            (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine.Point,
          (m = AddMonoidHom.id _ ∨ m = σ ∨ m = σ.comp σ ∨
              m = i ∨ m = i.comp σ ∨ m = i.comp (σ.comp σ) ∨
              m = j ∨ m = j.comp σ ∨ m = j.comp (σ.comp σ) ∨
              m = i.comp j ∨ m = (i.comp j).comp σ ∨ m = (i.comp j).comp (σ.comp σ)) →
        ∃ γ : VariableChange K, γ • (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K) = ⟨0, 0, 1, 0, 0⟩ ∧
          ∀ T, HEq (Point.vcInvFun γ (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine T) (m T)) := by
  refine ⟨σH ω hω, iH ω hω, jH ω hω, ?_, ?_, ?_, σσσ ω hω, ii ω hω, jj ω hω, ij_eq_neg_ji ω hω,
    σi_eq_jσ ω hω, σj_eq_jiσ ω hω, forall_stab ω hω, forall_twelve ω hω⟩
  · exact fun T => heq_vcHom _ (E K) (sigma_stab ω hω) T
  · exact fun T => heq_vcHom _ (E K) (i_stab ω hω) T
  · exact fun T => heq_vcHom _ (E K) (j_stab ω hω) T

#print axioms solution

end S_WeierstrassCurve_exists_addMonoidHom_omega_i_j_vcInvFun_of_char_two
end P2MW
export P2MW.S_WeierstrassCurve_exists_addMonoidHom_omega_i_j_vcInvFun_of_char_two (solution)
