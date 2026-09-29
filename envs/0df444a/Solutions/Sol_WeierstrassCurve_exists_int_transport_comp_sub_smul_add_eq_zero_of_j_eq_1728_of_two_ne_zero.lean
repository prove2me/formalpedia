-- Prove2me | solution 1 for WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_1728_of_two_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/4624632b-9ba2-5d56-9269-cb287f5cc7bb

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_equivOfVariableChangeEq_symm_conj_vcInvFun
import Theorems.Thm_WeierstrassCurve_mem_stabilizer_variableChange_iff_of_isShortNF_of_a6_eq_zero
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_1728_of_two_ne_zero

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace T1728E100

variable {K : Type*} [Field K] [DecidableEq K]

def AutTraceConcl (E : WeierstrassCurve K) (α : VariableChange K) (hα : α • E = E) : Prop :=
  ∃ t : ℤ, (t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧
    (∀ T : E.toAffine.Point,
      (Point.equivOfVariableChangeEq (W := E.toAffine) hα).symm
          ((Point.equivOfVariableChangeEq (W := E.toAffine) hα).symm T)
        - t • (Point.equivOfVariableChangeEq (W := E.toAffine) hα).symm T + T = 0) ∧
    (t = 2 → ∀ T : E.toAffine.Point, (Point.equivOfVariableChangeEq (W := E.toAffine) hα).symm T = T) ∧
    (t = -2 → ∀ T : E.toAffine.Point, (Point.equivOfVariableChangeEq (W := E.toAffine) hα).symm T = -T)

def castPt {V V' : WeierstrassCurve.Affine K} (h : V = V') (P : V.Point) : V'.Point := h ▸ P

theorem equivOfVariableChangeEq_symm_apply_eq_castPt {V W : WeierstrassCurve.Affine K}
    (C : VariableChange K) (h : C • W = V) (T : W.Point) :
    (Point.equivOfVariableChangeEq (C := C) (W := W) h).symm T = castPt h (Point.vcInvFun C W T) := by
  subst h; rfl

omit [DecidableEq K] in
theorem castPt_vcInvFun_zero (E : WeierstrassCurve K) (γ : VariableChange K) (hγ : γ • E = E) :
    castPt hγ (Point.vcInvFun γ E.toAffine 0) = 0 := by
  have key : ∀ (V : WeierstrassCurve K) (hV : γ • E = V),
      castPt hV (Point.vcInvFun γ E.toAffine 0) = 0 := by
    intro V hV; subst hV; rfl
  exact key E hγ

omit [DecidableEq K] in
theorem castPt_vcInvFun_some (E : WeierstrassCurve K) (γ : VariableChange K) (hγ : γ • E = E)
    (x y : K) (h : E.toAffine.Nonsingular x y) :
    ∃ h', castPt hγ (Point.vcInvFun γ E.toAffine (Point.some x y h)) =
      Point.some (vcXInv γ x) (vcYInv γ x y) h' := by
  have key : ∀ (V : WeierstrassCurve K) (hV : γ • E = V),
      ∃ h', castPt hV (Point.vcInvFun γ E.toAffine (Point.some x y h)) =
        Point.some (vcXInv γ x) (vcYInv γ x y) h' := by
    intro V hV; subst hV; exact ⟨_, rfl⟩
  exact key E hγ

omit [DecidableEq K] in
theorem point_some_eq_some {W : Affine K} {x₁ y₁ x₂ y₂ : K} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂} :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx hy; rfl

theorem autTraceConcl_of_isShortNF_a₆ (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsShortNF] (ha₆ : W.a₆ = 0) (ha₄ : W.a₄ ≠ 0)
    (γ : VariableChange K) (hγ : γ • W = W) : AutTraceConcl W γ hγ := by
  obtain ⟨hr, hs, ht, hu4⟩ :=
    (WeierstrassCurve.mem_stabilizer_variableChange_iff_of_isShortNF_of_a6_eq_zero h2 h3 W ha₆ ha₄ γ).mp
      (MulAction.mem_stabilizer_iff.mpr hγ)
  have hw4 : ((γ.u⁻¹ : Kˣ) : K) ^ 4 = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, hu4, inv_one]
  have hσ : ∀ T : W.toAffine.Point, (Point.equivOfVariableChangeEq (W := W.toAffine) hγ).symm T =
      castPt hγ (Point.vcInvFun γ W.toAffine T) :=
    fun T => equivOfVariableChangeEq_symm_apply_eq_castPt (W := W.toAffine) γ hγ T
  have hσ0 : castPt hγ (Point.vcInvFun γ W.toAffine 0) = 0 := castPt_vcInvFun_zero W γ hγ
  have hσ0' : castPt hγ (Point.vcInvFun γ W.toAffine Point.zero) = 0 := hσ0
  have hσsome : ∀ (x y : K) (h : W.toAffine.Nonsingular x y), ∃ h',
      castPt hγ (Point.vcInvFun γ W.toAffine (Point.some x y h)) =
        Point.some (((γ.u⁻¹ : Kˣ) : K) ^ 2 * x) (((γ.u⁻¹ : Kˣ) : K) ^ 3 * y) h' := by
    intro x y h
    obtain ⟨h', e⟩ := castPt_vcInvFun_some W γ hγ x y h
    have hX : vcXInv γ x = ((γ.u⁻¹ : Kˣ) : K) ^ 2 * x := by
      simp only [vcXInv, hr, sub_zero]
    have hY : vcYInv γ x y = ((γ.u⁻¹ : Kˣ) : K) ^ 3 * y := by
      simp only [vcYInv, hr, hs, ht, sub_zero, zero_mul]
    refine ⟨by rw [← hX, ← hY]; exact h', ?_⟩
    rw [e]
    exact point_some_eq_some hX hY
  unfold AutTraceConcl
  simp only [hσ]
  set w : K := ((γ.u⁻¹ : Kˣ) : K) with hw
  by_cases hw2 : w ^ 2 = 1
  ·
    have hw1 : w = 1 ∨ w = -1 := by
      have : (w - 1) * (w + 1) = 0 := by linear_combination hw2
      rcases mul_eq_zero.mp this with h | h
      · left; linear_combination h
      · right; linear_combination h
    rcases hw1 with hw1 | hw1
    ·
      have hfix : ∀ T : W.toAffine.Point, castPt hγ (Point.vcInvFun γ W.toAffine T) = T := by
        rintro (_ | ⟨x, y, h⟩)
        · exact hσ0
        · obtain ⟨h', e⟩ := hσsome x y h
          rw [e]
          exact point_some_eq_some (by rw [hw1]; ring) (by rw [hw1]; ring)
      refine ⟨2, Or.inr (Or.inr (Or.inr (Or.inr rfl))), fun T => ?_, fun _ => hfix, fun h => ?_⟩
      · rw [hfix, hfix]; abel
      · norm_num at h
    ·
      have hneg : ∀ T : W.toAffine.Point, castPt hγ (Point.vcInvFun γ W.toAffine T) = -T := by
        rintro (_ | ⟨x, y, h⟩)
        · exact hσ0
        · obtain ⟨h', e⟩ := hσsome x y h
          rw [e, Point.neg_some]
          refine point_some_eq_some (by rw [hw1]; ring) ?_
          simp only [negY, W.a₁_of_isShortNF, W.a₃_of_isShortNF]
          rw [hw1]; ring
      refine ⟨-2, Or.inl rfl, fun T => ?_, fun h => ?_, fun _ => hneg⟩
      · rw [hneg T, hneg (-T)]; abel
      · norm_num at h
  ·
    have hw2' : w ^ 2 = -1 := by
      have : (w ^ 2 - 1) * (w ^ 2 + 1) = 0 := by linear_combination hw4
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (by linear_combination h) hw2
      · linear_combination h
    refine ⟨0, Or.inr (Or.inr (Or.inl rfl)), ?_, fun h => ?_, fun h => ?_⟩
    · rintro (_ | ⟨x, y, h⟩)
      · rw [hσ0', hσ0]; simp [Point.zero_def]
      · obtain ⟨h₁, e₁⟩ := hσsome x y h
        obtain ⟨h₂, e₂⟩ := hσsome (w ^ 2 * x) (w ^ 3 * y) h₁
        rw [e₁, e₂, zero_zsmul, sub_zero]
        have e₃ : (Point.some (w ^ 2 * (w ^ 2 * x)) (w ^ 3 * (w ^ 3 * y)) h₂ : W.toAffine.Point) =
            -Point.some x y h := by
          rw [Point.neg_some]
          refine point_some_eq_some ?_ ?_
          · have e : w ^ 2 * (w ^ 2 * x) = (w ^ 2) ^ 2 * x := by ring
            rw [e, hw2']; ring
          · simp only [negY, W.a₁_of_isShortNF, W.a₃_of_isShortNF]
            have e : w ^ 3 * (w ^ 3 * y) = (w ^ 2) ^ 3 * y := by ring
            rw [e, hw2']; ring
        rw [e₃]
        exact neg_add_cancel _
    · norm_num at h
    · norm_num at h

omit [DecidableEq K] in

theorem c₆_eq_zero_of_j_eq (E : WeierstrassCurve K) [E.IsElliptic] (hj : E.j = 1728) : E.c₆ = 0 := by
  have hΔ : E.Δ ≠ 0 := E.isUnit_Δ.ne_zero
  have hc43 : E.c₄ ^ 3 = 1728 * E.Δ := by
    have h := hj
    rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ'] at h
    calc E.c₄ ^ 3 = E.Δ * (E.Δ⁻¹ * E.c₄ ^ 3) := by
          rw [← mul_assoc, mul_inv_cancel₀ hΔ, one_mul]
      _ = E.Δ * 1728 := by rw [h]
      _ = 1728 * E.Δ := mul_comm _ _
  have hsq : E.c₆ ^ 2 = 0 := by linear_combination hc43 + E.c_relation
  exact pow_eq_zero_iff two_ne_zero |>.mp hsq

theorem autTraceConcl_of_conj (E : WeierstrassCurve K) (C α : VariableChange K) (hα : α • E = E)
    (hγ' : (C * α * C⁻¹) • (C • E) = C • E)
    (hconj : ∀ T : E.toAffine.Point,
      (Point.equivOfVariableChangeEq (W := (C • E).toAffine) hγ').symm (Point.vcInvFun C E.toAffine T) =
        Point.vcInvFun C E.toAffine ((Point.equivOfVariableChangeEq (W := E.toAffine) hα).symm T))
    (h : AutTraceConcl (C • E) (C * α * C⁻¹) hγ') : AutTraceConcl E α hα := by
  obtain ⟨t, ht, hrel, hp2, hm2⟩ := h

  let ι : E.toAffine.Point →+ (C • E).toAffine.Point :=
    AddMonoidHom.mk' (Point.vcInvFun C E.toAffine) (Point.vcInvFun_add C E.toAffine)
  have hι : ∀ T, ι T = Point.vcInvFun C E.toAffine T := fun T => rfl
  have hinj : Function.Injective ι := fun P Q hPQ =>
    (Point.vcFun_rightInverse (C := C) (W := E.toAffine)).injective hPQ
  refine ⟨t, ht, fun T => hinj ?_, fun h2 T => hinj ?_, fun h2 T => hinj ?_⟩
  · have key := hrel (Point.vcInvFun C E.toAffine T)
    rw [hconj, hconj] at key
    rw [map_add, map_sub, map_zsmul, map_zero]
    exact key
  · rw [hι, hι, ← hconj]
    exact hp2 h2 _
  · rw [map_neg, hι, hι, ← hconj]
    exact hm2 h2 _

end T1728E100

open T1728E100 in

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (hj : E₀.j = 1728)
    (α : WeierstrassCurve.VariableChange K) (hα : α • E₀ = E₀) :
    ∃ t : ℤ, (t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧
      (∀ T : E₀.toAffine.Point,
        (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm
            ((Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T)
          - t • (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T + T = 0) ∧
      (t = 2 → ∀ T : E₀.toAffine.Point, (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T = T) ∧
      (t = -2 → ∀ T : E₀.toAffine.Point, (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T = -T) := by
  letI : Invertible (2 : K) := invertibleOfNonzero h2
  letI : Invertible (3 : K) := invertibleOfNonzero h3

  have hjW : (E₀.toShortNF • E₀).j = 1728 := by rw [variableChange_j, hj]
  have hc₆ := c₆_eq_zero_of_j_eq (E₀.toShortNF • E₀) hjW
  have h864 : (-864 : K) ≠ 0 := fun habs =>
    mul_ne_zero (pow_ne_zero 5 h2) (pow_ne_zero 3 h3) (by linear_combination -habs)
  have ha₆ : (E₀.toShortNF • E₀).a₆ = 0 := by
    rw [(E₀.toShortNF • E₀).c₆_of_isShortNF] at hc₆
    exact (mul_eq_zero.mp hc₆).resolve_left h864
  have ha₄ : (E₀.toShortNF • E₀).a₄ ≠ 0 := by
    intro h
    apply (E₀.toShortNF • E₀).isUnit_Δ.ne_zero
    rw [(E₀.toShortNF • E₀).Δ_of_isShortNF, ha₆, h]; ring
  obtain ⟨hγ', hconj⟩ :=
    WeierstrassCurve.equivOfVariableChangeEq_symm_conj_vcInvFun E₀ E₀.toShortNF α hα
  exact autTraceConcl_of_conj E₀ E₀.toShortNF α hα hγ' hconj
    (autTraceConcl_of_isShortNF_a₆ h2 h3 (E₀.toShortNF • E₀) ha₆ ha₄ _ hγ')

end S_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_1728_of_two_ne_zero
end P2MW
export P2MW.S_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero_of_j_eq_1728_of_two_ne_zero (solution)
