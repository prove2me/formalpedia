-- Prove2me | solution 1 for WeierstrassCurve.variableChange_smul_eq_self_iff_of_tateNormalForm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/2146fc33-d4ed-53d8-ae5e-da1a4e1017f2

import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.Tactic.LinearCombination
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_variableChange_smul_eq_self_iff_of_tateNormalForm

open WeierstrassCurve

theorem solution {K : Type*} [Field K] (E : WeierstrassCurve K)
    (ha₁ : E.a₁ = 1) (ha₂ : E.a₂ = 0) (ha₃ : E.a₃ = 0)
    (hc₄ : E.c₄ ≠ 0) (hc₆ : E.c₆ ≠ 0)
    (C : VariableChange K) :
    C • E = E ↔ C = 1 ∨ C = (⟨-1, 0, -1, 0⟩ : VariableChange K) := by

  have hιval : (↑(-1 : Kˣ) : K) = -1 := by rw [Units.val_neg, Units.val_one]
  have hιuK : (↑((-1 : Kˣ)⁻¹) : K) = -1 := by
    have h := (-1 : Kˣ).inv_mul
    rw [hιval] at h
    have h2 := congrArg (· * (-1 : K)) h
    simp only [mul_assoc, neg_mul_neg, one_mul, mul_one] at h2
    exact h2
  constructor
  ·
    intro hCE
    obtain ⟨u, r, s, t⟩ := C
    have hvine : (↑u⁻¹ : K) ≠ 0 := u⁻¹.ne_zero

    have eqa₁ : (↑u⁻¹ : K) * (1 + 2 * s) = 1 := by
      have := congrArg WeierstrassCurve.a₁ hCE; rwa [variableChange_a₁, ha₁] at this
    have eqa₂ : (↑u⁻¹ : K) ^ 2 * (-s + 3 * r - s ^ 2) = 0 := by
      have := congrArg WeierstrassCurve.a₂ hCE
      rw [variableChange_a₂, ha₁, ha₂] at this; simpa using this
    have eqa₃ : (↑u⁻¹ : K) ^ 3 * (r + 2 * t) = 0 := by
      have := congrArg WeierstrassCurve.a₃ hCE
      rw [variableChange_a₃, ha₁, ha₃] at this; simpa using this
    have eqa₄ : (↑u⁻¹ : K) ^ 4 * (E.a₄ - (t + r * s) + 3 * r ^ 2 - 2 * s * t) = E.a₄ := by
      have := congrArg WeierstrassCurve.a₄ hCE
      rw [variableChange_a₄, ha₁, ha₂, ha₃] at this; simpa using this
    have eqa₆ : (↑u⁻¹ : K) ^ 6 * (E.a₆ + r * E.a₄ + r ^ 3 - t ^ 2 - r * t) = E.a₆ := by
      have := congrArg WeierstrassCurve.a₆ hCE
      rw [variableChange_a₆, ha₁, ha₂, ha₃] at this; simpa using this
    have eqc₄ : (↑u⁻¹ : K) ^ 4 * E.c₄ = E.c₄ := by
      have := congrArg WeierstrassCurve.c₄ hCE; rwa [variableChange_c₄] at this
    have eqc₆ : (↑u⁻¹ : K) ^ 6 * E.c₆ = E.c₆ := by
      have := congrArg WeierstrassCurve.c₆ hCE; rwa [variableChange_c₆] at this

    have hui4 : (↑u⁻¹ : K) ^ 4 = 1 :=
      mul_right_cancel₀ hc₄ (by rw [eqc₄, one_mul])
    have hui6 : (↑u⁻¹ : K) ^ 6 = 1 :=
      mul_right_cancel₀ hc₆ (by rw [eqc₆, one_mul])
    have hui2 : (↑u⁻¹ : K) ^ 2 = 1 := by
      have h := hui6; rw [show (6:ℕ) = 2 + 4 from rfl, pow_add, hui4, mul_one] at h; exact h

    have h1 : 1 + 2 * s = (↑u : K) := by
      have key : (↑u : K) * ((↑u⁻¹ : K) * (1 + 2 * s)) = (↑u : K) * 1 := by rw [eqa₁]
      rwa [← mul_assoc, u.mul_inv, one_mul, mul_one] at key
    have h2 : 3 * r = s + s ^ 2 := by
      have h := eqa₂; rw [hui2, one_mul] at h; linear_combination h
    have h3 : r + 2 * t = 0 :=
      (mul_eq_zero.mp eqa₃).resolve_left (pow_ne_zero _ hvine)
    have h4 : 3 * r ^ 2 - t - r * s - 2 * s * t = 0 := by
      have h := eqa₄; rw [hui4, one_mul] at h; linear_combination h
    have h6 : r * E.a₄ + r ^ 3 - t ^ 2 - r * t = 0 := by
      have h := eqa₆; rw [hui6, one_mul] at h; linear_combination h

    have hv2 : (↑u : K) ^ 2 = 1 := by
      have hmul : (↑u⁻¹ : K) ^ 2 * (↑u : K) ^ 2 = 1 := by rw [← mul_pow, u.inv_mul, one_pow]
      rw [hui2, one_mul] at hmul; exact hmul
    have hvcases : (↑u : K) = 1 ∨ (↑u : K) = -1 := by
      have hprod : ((↑u : K) - 1) * ((↑u : K) + 1) = 0 := by
        have hfac : ((↑u : K) - 1) * ((↑u : K) + 1) = (↑u : K) ^ 2 - 1 := by ring
        rw [hfac, hv2, sub_self]
      rcases mul_eq_zero.mp hprod with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)

    have h6r : (6 : K) * r = 0 := by
      rcases hvcases with hv1 | hv1
      · have h2s0 : 2 * s = 0 := by linear_combination h1 + hv1
        linear_combination 2 * h2 + (1 + s) * h2s0
      · have h2s1 : 2 * (s + 1) = 0 := by linear_combination h1 + hv1
        linear_combination 2 * h2 + s * h2s1

    have hr : r = 0 := by linear_combination 2 * h4 + (1 + 2 * s) * h3 - r * h6r

    have ht : t = 0 := by
      have ht2 : t ^ 2 = 0 := by linear_combination -h6 + E.a₄ * hr + r ^ 2 * hr - t * hr
      exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp ht2

    have hss : s * (1 + s) = 0 := by linear_combination -h2 + 3 * hr
    rcases mul_eq_zero.mp hss with hs | hs
    · left
      have hv1 : (↑u : K) = 1 := by linear_combination -h1 + 2 * hs
      have hu1 : u = 1 := Units.ext (by rw [Units.val_one]; exact hv1)
      rw [VariableChange.one_def]
      exact VariableChange.ext hu1 hr hs ht
    · right
      have hs' : s = -1 := by linear_combination hs
      have hvm1 : (↑u : K) = -1 := by linear_combination -h1 + 2 * hs
      have hum1 : u = -1 := Units.ext (by rw [Units.val_neg, Units.val_one]; exact hvm1)
      exact VariableChange.ext hum1 hr hs' ht
  ·
    rintro (rfl | rfl)
    · exact one_smul _ E
    · refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
      · show (↑((-1 : Kˣ)⁻¹) : K) * (E.a₁ + 2 * (-1)) = E.a₁
        rw [hιuK, ha₁]; ring
      · show (↑((-1 : Kˣ)⁻¹) : K) ^ 2 * (E.a₂ - (-1) * E.a₁ + 3 * 0 - (-1) ^ 2) = E.a₂
        rw [hιuK, ha₁, ha₂]; ring
      · show (↑((-1 : Kˣ)⁻¹) : K) ^ 3 * (E.a₃ + 0 * E.a₁ + 2 * 0) = E.a₃
        rw [hιuK, ha₃]; ring
      · show (↑((-1 : Kˣ)⁻¹) : K) ^ 4
            * (E.a₄ - (-1) * E.a₃ + 2 * 0 * E.a₂ - (0 + 0 * (-1)) * E.a₁ + 3 * 0 ^ 2
                - 2 * (-1) * 0) = E.a₄
        rw [hιuK, ha₃]; ring
      · show (↑((-1 : Kˣ)⁻¹) : K) ^ 6
            * (E.a₆ + 0 * E.a₄ + 0 ^ 2 * E.a₂ + 0 ^ 3 - 0 * E.a₃ - 0 ^ 2 - 0 * 0 * E.a₁) = E.a₆
        rw [hιuK]; ring

end S_WeierstrassCurve_variableChange_smul_eq_self_iff_of_tateNormalForm
end P2MW
export P2MW.S_WeierstrassCurve_variableChange_smul_eq_self_iff_of_tateNormalForm (solution)
