-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_of_j_eq_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/02dc11c5-e048-5f77-ac1a-7be0cdb4b45a

import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Theorems.Thm_WeierstrassCurve_exists_variableChange_of_isShortNF_of_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_of_j_eq_of_sq

open WeierstrassCurve

section Helpers
variable {F : Type*} [Field F]

lemma j_eq_1728_of_c₆_eq_zero (E : WeierstrassCurve F) [E.IsElliptic] (h : E.c₆ = 0) :
    E.j = 1728 := by
  have hΔ : E.Δ ≠ 0 := E.isUnit_Δ.ne_zero
  have h17 : E.c₄ ^ 3 = 1728 * E.Δ := by linear_combination -E.c_relation + E.c₆ * h
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', h17,
    mul_comm (1728 : F) E.Δ, ← mul_assoc, inv_mul_cancel₀ hΔ, one_mul]

lemma c₄_pow_three_mul_Δ_eq_of_j_eq (E E' : WeierstrassCurve F) [E.IsElliptic] [E'.IsElliptic]
    (heq : E.j = E'.j) : E.c₄ ^ 3 * E'.Δ = E'.c₄ ^ 3 * E.Δ := by
  have hΔ : E.Δ ≠ 0 := E.isUnit_Δ.ne_zero
  have hΔ' : E'.Δ ≠ 0 := E'.isUnit_Δ.ne_zero
  have h := heq
  simp only [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ'] at h

  have h2 := congrArg (fun x : F => x * (E.Δ * E'.Δ)) h
  rw [show E.Δ⁻¹ * E.c₄ ^ 3 * (E.Δ * E'.Δ) = E.Δ⁻¹ * E.Δ * (E.c₄ ^ 3 * E'.Δ) by ring,
    show E'.Δ⁻¹ * E'.c₄ ^ 3 * (E.Δ * E'.Δ) = E'.Δ⁻¹ * E'.Δ * (E'.c₄ ^ 3 * E.Δ) by ring,
    inv_mul_cancel₀ hΔ, inv_mul_cancel₀ hΔ', one_mul, one_mul] at h2
  exact h2

section ToShortNF

variable {R : Type*} [CommRing R] [Invertible (2 : R)] [Invertible (3 : R)]
  (W : WeierstrassCurve R)

lemma toShortNF_u : W.toShortNF.u = 1 := by
  simp [toShortNF, toCharNeTwoNF, VariableChange.mul_def]

lemma toShortNF_smul_c₄ : (W.toShortNF • W).c₄ = W.c₄ := by
  simp only [variableChange_c₄, toShortNF_u, inv_one, Units.val_one, one_pow, one_mul]

lemma toShortNF_smul_c₆ : (W.toShortNF • W).c₆ = W.c₆ := by
  simp only [variableChange_c₆, toShortNF_u, inv_one, Units.val_one, one_pow, one_mul]

end ToShortNF

end Helpers

theorem solution {F : Type*} [Field F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (E E' : WeierstrassCurve F) [E.IsElliptic] [E'.IsElliptic]
    (heq : E.j = E'.j) (hj0 : E.j ≠ 0) (hj1728 : E.j ≠ 1728)
    {s : F} (hs : s ^ 2 = E.c₆ * E'.c₄ / (E'.c₆ * E.c₄)) :
    ∃ C : VariableChange F, C • E = E' := by
  letI : Invertible (2 : F) := invertibleOfNonzero h2
  letI : Invertible (3 : F) := invertibleOfNonzero h3

  have hj0' : E'.j ≠ 0 := by rw [← heq]; exact hj0
  have hj1728' : E'.j ≠ 1728 := by rw [← heq]; exact hj1728
  have hc₄ : E.c₄ ≠ 0 := fun h => hj0 (E.j_eq_zero h)
  have hc₄' : E'.c₄ ≠ 0 := fun h => hj0' (E'.j_eq_zero h)
  have hc₆ : E.c₆ ≠ 0 := fun h => hj1728 (j_eq_1728_of_c₆_eq_zero E h)
  have hc₆' : E'.c₆ ≠ 0 := fun h => hj1728' (j_eq_1728_of_c₆_eq_zero E' h)

  have hc₄E : (E.toShortNF • E).c₄ = E.c₄ := toShortNF_smul_c₄ E
  have hc₆E : (E.toShortNF • E).c₆ = E.c₆ := toShortNF_smul_c₆ E
  have hc₄E' : (E'.toShortNF • E').c₄ = E'.c₄ := toShortNF_smul_c₄ E'
  have hc₆E' : (E'.toShortNF • E').c₆ = E'.c₆ := toShortNF_smul_c₆ E'

  have e₁ : E.c₄ = -48 * (E.toShortNF • E).a₄ :=
    hc₄E.symm.trans (E.toShortNF • E).c₄_of_isShortNF
  have e₂ : E.c₆ = -864 * (E.toShortNF • E).a₆ :=
    hc₆E.symm.trans (E.toShortNF • E).c₆_of_isShortNF
  have e₃ : E'.c₄ = -48 * (E'.toShortNF • E').a₄ :=
    hc₄E'.symm.trans (E'.toShortNF • E').c₄_of_isShortNF
  have e₄ : E'.c₆ = -864 * (E'.toShortNF • E').a₆ :=
    hc₆E'.symm.trans (E'.toShortNF • E').c₆_of_isShortNF

  have ha₄s : (E.toShortNF • E).a₄ ≠ 0 := fun h => hc₄ (by rw [e₁, h, mul_zero])
  have ha₆s : (E.toShortNF • E).a₆ ≠ 0 := fun h => hc₆ (by rw [e₂, h, mul_zero])
  have ha₄s' : (E'.toShortNF • E').a₄ ≠ 0 := fun h => hc₄' (by rw [e₃, h, mul_zero])
  have ha₆s' : (E'.toShortNF • E').a₆ ≠ 0 := fun h => hc₆' (by rw [e₄, h, mul_zero])

  have heq_s : (E.toShortNF • E).j = (E'.toShortNF • E').j := by
    rw [variableChange_j, variableChange_j]; exact heq
  have hkey := c₄_pow_three_mul_Δ_eq_of_j_eq (E.toShortNF • E) (E'.toShortNF • E') heq_s
  rw [(E.toShortNF • E).c₄_of_isShortNF, (E'.toShortNF • E').c₄_of_isShortNF,
    (E.toShortNF • E).Δ_of_isShortNF, (E'.toShortNF • E').Δ_of_isShortNF] at hkey
  have hrel : (E.toShortNF • E).a₄ ^ 3 * (E'.toShortNF • E').a₆ ^ 2
      = (E'.toShortNF • E').a₄ ^ 3 * (E.toShortNF • E).a₆ ^ 2 := by
    letI : Invertible (47775744 : F) := invertibleOfNonzero (by
      have h := mul_ne_zero (pow_ne_zero 16 h2) (pow_ne_zero 6 h3)
      norm_num1 at h
      exact h)
    rw [← mul_right_inj_of_invertible (47775744 : F)]
    linear_combination hkey

  have hsA : s ^ 2 * ((E'.toShortNF • E').a₆ * (E.toShortNF • E).a₄)
      = (E.toShortNF • E).a₆ * (E'.toShortNF • E').a₄ := by
    have hden : E'.c₆ * E.c₄ ≠ 0 := mul_ne_zero hc₆' hc₄
    rw [eq_div_iff hden] at hs
    rw [e₁, e₂, e₃, e₄] at hs
    letI : Invertible (41472 : F) := invertibleOfNonzero (by
      have h := mul_ne_zero (pow_ne_zero 9 h2) (pow_ne_zero 4 h3)
      norm_num1 at h
      exact h)
    rw [← mul_right_inj_of_invertible (41472 : F)]
    linear_combination hs

  obtain ⟨C, hC⟩ := exists_variableChange_of_isShortNF_of_sq (E.toShortNF • E)
    (E'.toShortNF • E') ha₄s ha₆s ha₄s' ha₆s' hrel hsA
  refine ⟨E'.toShortNF⁻¹ * C * E.toShortNF, ?_⟩
  rw [mul_smul, mul_smul, hC, inv_smul_smul]

end S_WeierstrassCurve_exists_variableChange_of_j_eq_of_sq
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_of_j_eq_of_sq (solution)
