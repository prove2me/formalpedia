-- Prove2me | solution 1 for WeierstrassCurve.exists_int_transport_comp_sub_smul_add_eq_zero_of_natCard_stabilizer_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/6c5a6088-03d6-5288-9261-fe7df89cbcec

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_one_heq
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_neg_heq_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero_of_natCard_stabilizer_eq_two

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace TGENE100

variable {K : Type*} [Field K] [DecidableEq K]

def castPt {V V' : WeierstrassCurve.Affine K} (h : V = V') (P : V.Point) : V'.Point := h ▸ P

omit [DecidableEq K] in
theorem heq_iff_castPt_eq {V V' : WeierstrassCurve.Affine K} (h : V = V') (P : V.Point)
    (Q : V'.Point) : HEq P Q ↔ castPt h P = Q := by
  subst h; simp [castPt]

theorem equivOfVariableChangeEq_symm_apply_eq_castPt {V W : WeierstrassCurve.Affine K}
    (C : VariableChange K) (h : C • W = V) (T : W.Point) :
    (Point.equivOfVariableChangeEq (C := C) (W := W) h).symm T = castPt h (Point.vcInvFun C W T) := by
  subst h; rfl

section neg

variable (E : WeierstrassCurve K)

def negVC : VariableChange K := ⟨-1, 0, -E.a₁, -E.a₃⟩

omit [DecidableEq K] in
theorem negVC_smul : negVC E • E = E := by
  ext <;> simp [negVC, WeierstrassCurve.variableChange_def] <;> ring

omit [DecidableEq K] in
theorem negVC_ne_one [E.IsElliptic] : negVC E ≠ 1 := by
  intro h
  have hu : (((negVC E).u : Kˣ) : K) = ((1 : VariableChange K).u : K) := by rw [h]
  have hs : (negVC E).s = (1 : VariableChange K).s := by rw [h]
  have ht : (negVC E).t = (1 : VariableChange K).t := by rw [h]
  simp only [negVC, VariableChange.one_def, Units.val_neg, Units.val_one, neg_eq_zero] at hu hs ht
  have h2 : (2 : K) = 0 := by linear_combination -hu
  have h4 : (4 : K) = 0 := by linear_combination 2 * h2
  have hb2 : E.b₂ = 0 := by rw [WeierstrassCurve.b₂, hs]; linear_combination E.a₂ * h4
  have hb4 : E.b₄ = 0 := by rw [WeierstrassCurve.b₄, hs, ht]; linear_combination E.a₄ * h2
  have hb6 : E.b₆ = 0 := by rw [WeierstrassCurve.b₆, ht]; linear_combination E.a₆ * h4
  have hΔ : E.Δ = 0 := by rw [WeierstrassCurve.Δ, hb2, hb4, hb6]; ring
  exact E.isUnit_Δ.ne_zero hΔ

theorem castPt_vcInvFun_negVC (h : negVC E • E = E) (T : E.toAffine.Point) :
    castPt h (Point.vcInvFun (negVC E) E.toAffine T) = -T :=
  (heq_iff_castPt_eq _ _ _).mp (Point.vcInvFun_neg_heq_neg E T)

theorem castPt_vcInvFun_one (h : (1 : VariableChange K) • E = E) (T : E.toAffine.Point) :
    castPt h (Point.vcInvFun (1 : VariableChange K) E.toAffine T) = T :=
  (heq_iff_castPt_eq _ _ _).mp (Point.vcInvFun_one_heq E.toAffine T)

theorem eq_one_or_eq_negVC [E.IsElliptic]
    (h2 : Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange K) E) = 2)
    (α : VariableChange K) (hα : α • E = E) : α = 1 ∨ α = negVC E := by
  by_cases hα1 : α = 1
  · exact Or.inl hα1
  · right
    obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff'
      (1 : MulAction.stabilizer (WeierstrassCurve.VariableChange K) E)).mp h2
    have ha : (⟨α, MulAction.mem_stabilizer_iff.mpr hα⟩ :
        MulAction.stabilizer (WeierstrassCurve.VariableChange K) E) = y :=
      huniq _ (fun h => hα1 (congrArg Subtype.val h))
    have hn : (⟨negVC E, MulAction.mem_stabilizer_iff.mpr (negVC_smul E)⟩ :
        MulAction.stabilizer (WeierstrassCurve.VariableChange K) E) = y :=
      huniq _ (fun h => negVC_ne_one E (congrArg Subtype.val h))
    exact congrArg Subtype.val (ha.trans hn.symm)

end neg

end TGENE100

open TGENE100 in

theorem solution
    (K : Type*) [Field K] [DecidableEq K]
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    (h2 : Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange K) E₀) = 2)
    (α : WeierstrassCurve.VariableChange K) (hα : α • E₀ = E₀) :
    ∃ t : ℤ, (t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) ∧
      (∀ T : E₀.toAffine.Point,
        (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm
            ((Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T)
          - t • (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T + T = 0) ∧
      (t = 2 → ∀ T : E₀.toAffine.Point, (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T = T) ∧
      (t = -2 → ∀ T : E₀.toAffine.Point, (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T = -T) := by

  have hσ : ∀ T : E₀.toAffine.Point,
      (Point.equivOfVariableChangeEq (W := E₀.toAffine) hα).symm T =
        castPt hα (Point.vcInvFun α E₀.toAffine T) :=
    fun T => equivOfVariableChangeEq_symm_apply_eq_castPt (W := E₀.toAffine) α hα T
  simp only [hσ]
  rcases eq_one_or_eq_negVC E₀ h2 α hα with rfl | rfl
  ·
    have hfix : ∀ T : E₀.toAffine.Point,
        castPt hα (Point.vcInvFun (1 : VariableChange K) E₀.toAffine T) = T :=
      castPt_vcInvFun_one E₀ hα
    refine ⟨2, Or.inr (Or.inr (Or.inr (Or.inr rfl))), fun T => ?_, fun _ => hfix, fun h => ?_⟩
    · rw [hfix, hfix]; abel
    · norm_num at h
  ·
    have hneg : ∀ T : E₀.toAffine.Point,
        castPt hα (Point.vcInvFun (negVC E₀) E₀.toAffine T) = -T :=
      castPt_vcInvFun_negVC E₀ hα
    refine ⟨-2, Or.inl rfl, fun T => ?_, fun h => ?_, fun _ => hneg⟩
    · rw [hneg T, hneg (-T)]; abel
    · norm_num at h

end S_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero_of_natCard_stabilizer_eq_two
end P2MW
export P2MW.S_WeierstrassCurve_exists_int_transport_comp_sub_smul_add_eq_zero_of_natCard_stabilizer_eq_two (solution)
