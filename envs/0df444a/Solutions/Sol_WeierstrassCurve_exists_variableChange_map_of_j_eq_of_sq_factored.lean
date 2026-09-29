-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_map_of_j_eq_of_sq_factored
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/9f4fd99c-aa4e-5fb2-9c43-3de0f7772489

import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.Tactic.LinearCombination
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_map_of_j_eq_of_sq_factored

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "a₃_of_isShortNF toCharNeTwoNF isUnit_Δ VariableChange.mul_def variableChange_c₆ variableChange_j c_relation Δ_of_isShortNF c₄_of_isShortNF a₁_of_isShortNF IsShortNF map toShortNF_spec coe_Δ' variableChange_a₃ a₂_of_isShortNF a₄ a₆ c₆_of_isShortNF toShortNF variableChange_a₆ c₆ variableChange_a₂ variableChange_c₄ map_a₆ variableChange_a₁ map_a₁ map_a₄ variableChange_a₄ Δ c₄ VariableChange map_a₂ map_variableChange j_eq_zero j map_a₃"
p2m_open "WeierstrassCurve"
p2m_open "WeierstrassCurve.VariableChange"

private lemma toShortNF_u' {R : Type*} [CommRing R] [Invertible (2:R)] [Invertible (3:R)]
    (W : WeierstrassCurve R) : W.toShortNF.u = 1 := by
  simp [toShortNF, toCharNeTwoNF, VariableChange.mul_def]

private lemma j_eq_1728_of_c₆_eq_zero' {F : Type*} [Field F] (E : WeierstrassCurve F)
    [E.IsElliptic] (h : E.c₆ = 0) : E.j = 1728 := by
  have hΔ : E.Δ ≠ 0 := E.isUnit_Δ.ne_zero
  have h17 : E.c₄ ^ 3 = 1728 * E.Δ := by linear_combination -E.c_relation + E.c₆ * h
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', h17,
    mul_comm (1728 : F) E.Δ, ← mul_assoc, inv_mul_cancel₀ hΔ, one_mul]

private lemma c₄_pow_three_mul_Δ_eq_of_j_eq' {F : Type*} [Field F]
    (E E' : WeierstrassCurve F) [E.IsElliptic] [E'.IsElliptic]
    (heq : E.j = E'.j) : E.c₄ ^ 3 * E'.Δ = E'.c₄ ^ 3 * E.Δ := by
  have hΔ : E.Δ ≠ 0 := E.isUnit_Δ.ne_zero
  have hΔ' : E'.Δ ≠ 0 := E'.isUnit_Δ.ne_zero
  have h := heq
  simp only [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ'] at h
  have h2 := congrArg (· * (E.Δ * E'.Δ)) h
  rw [show E.Δ⁻¹ * E.c₄ ^ 3 * (E.Δ * E'.Δ) = E.Δ⁻¹ * E.Δ * (E.c₄ ^ 3 * E'.Δ) from by ring,
    show E'.Δ⁻¹ * E'.c₄ ^ 3 * (E.Δ * E'.Δ) = E'.Δ⁻¹ * E'.Δ * (E'.c₄ ^ 3 * E.Δ) from by ring,
    inv_mul_cancel₀ hΔ, inv_mul_cancel₀ hΔ', one_mul, one_mul] at h2
  exact h2

theorem _root_.P2MW.S_WeierstrassCurve_exists_variableChange_map_of_j_eq_of_sq_factored.solution {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (E E' : WeierstrassCurve K) [E.IsElliptic] [E'.IsElliptic]
    (heq : E.j = E'.j) (hj0 : E.j ≠ 0) (hj1728 : E.j ≠ 1728)
    {s : L} (hs : s ^ 2 = f (E.c₆ * E'.c₄ / (E'.c₆ * E.c₄))) :
    ∃ (A B : VariableChange K) (hs0 : s ≠ 0),
      ((A.map f) * (⟨Units.mk0 s hs0, 0, 0, 0⟩ : VariableChange L) * (B.map f)) • E.map f
        = E'.map f := by
  letI : Invertible (2 : K) := invertibleOfNonzero h2
  letI : Invertible (3 : K) := invertibleOfNonzero h3
  have h2L : (2 : L) ≠ 0 := by rw [← map_ofNat f 2]; exact (map_ne_zero f).mpr h2
  have h3L : (3 : L) ≠ 0 := by rw [← map_ofNat f 3]; exact (map_ne_zero f).mpr h3
  letI : Invertible (2 : L) := invertibleOfNonzero h2L
  letI : Invertible (3 : L) := invertibleOfNonzero h3L

  have hj0' : E'.j ≠ 0 := heq ▸ hj0
  have hj1728' : E'.j ≠ 1728 := heq ▸ hj1728
  have hc₄ : E.c₄ ≠ 0 := fun h => hj0 (E.j_eq_zero h)
  have hc₄' : E'.c₄ ≠ 0 := fun h => hj0' (E'.j_eq_zero h)
  have hc₆ : E.c₆ ≠ 0 := fun h => hj1728 (j_eq_1728_of_c₆_eq_zero' E h)
  have hc₆' : E'.c₆ ≠ 0 := fun h => hj1728' (j_eq_1728_of_c₆_eq_zero' E' h)

  have hdne : E.c₆ * E'.c₄ / (E'.c₆ * E.c₄) ≠ 0 :=
    div_ne_zero (mul_ne_zero hc₆ hc₄') (mul_ne_zero hc₆' hc₄)
  have hs0 : s ≠ 0 := fun h0 => by
    rw [h0, zero_pow two_ne_zero] at hs
    exact ((map_ne_zero f).mpr hdne) hs.symm

  refine ⟨E'.toShortNF⁻¹, E.toShortNF, hs0, ?_⟩

  set ES := E.toShortNF • E with hES
  set ES' := E'.toShortNF • E' with hES'
  haveI : ES.IsShortNF := E.toShortNF_spec
  haveI : ES'.IsShortNF := E'.toShortNF_spec

  have hu : E.toShortNF.u = 1 := toShortNF_u' E
  have hu' : E'.toShortNF.u = 1 := toShortNF_u' E'
  have hc₄E : ES.c₄ = E.c₄ := by
    rw [hES, variableChange_c₄, hu, inv_one, Units.val_one, one_pow, one_mul]
  have hc₆E : ES.c₆ = E.c₆ := by
    rw [hES, variableChange_c₆, hu, inv_one, Units.val_one, one_pow, one_mul]
  have hc₄E' : ES'.c₄ = E'.c₄ := by
    rw [hES', variableChange_c₄, hu', inv_one, Units.val_one, one_pow, one_mul]
  have hc₆E' : ES'.c₆ = E'.c₆ := by
    rw [hES', variableChange_c₆, hu', inv_one, Units.val_one, one_pow, one_mul]

  have e₁ : E.c₄ = -48 * ES.a₄ := hc₄E.symm.trans ES.c₄_of_isShortNF
  have e₂ : E.c₆ = -864 * ES.a₆ := hc₆E.symm.trans ES.c₆_of_isShortNF
  have e₃ : E'.c₄ = -48 * ES'.a₄ := hc₄E'.symm.trans ES'.c₄_of_isShortNF
  have e₄ : E'.c₆ = -864 * ES'.a₆ := hc₆E'.symm.trans ES'.c₆_of_isShortNF
  have ha₄s : ES.a₄ ≠ 0 := fun h => hc₄ (by rw [e₁, h, mul_zero])
  have ha₆s : ES.a₆ ≠ 0 := fun h => hc₆ (by rw [e₂, h, mul_zero])
  have ha₄s' : ES'.a₄ ≠ 0 := fun h => hc₄' (by rw [e₃, h, mul_zero])
  have ha₆s' : ES'.a₆ ≠ 0 := fun h => hc₆' (by rw [e₄, h, mul_zero])

  haveI : ES.IsElliptic := by rw [hES]; infer_instance
  haveI : ES'.IsElliptic := by rw [hES']; infer_instance
  have heq_s : ES.j = ES'.j := by
    simp only [hES, hES', variableChange_j]; exact heq
  have hkey := c₄_pow_three_mul_Δ_eq_of_j_eq' ES ES' heq_s
  rw [ES.c₄_of_isShortNF, ES'.c₄_of_isShortNF, ES.Δ_of_isShortNF, ES'.Δ_of_isShortNF] at hkey
  have hrel : ES.a₄ ^ 3 * ES'.a₆ ^ 2 = ES'.a₄ ^ 3 * ES.a₆ ^ 2 := by
    have h47 : (47775744 : K) ≠ 0 := by
      have := mul_ne_zero (pow_ne_zero 16 h2) (pow_ne_zero 6 h3); norm_num at this; exact this
    have := mul_right_cancel₀ h47
      (show ES.a₄^3 * ES'.a₆^2 * 47775744 = ES'.a₄^3 * ES.a₆^2 * 47775744 from by
        linear_combination hkey)
    exact this

  have hsA : s ^ 2 * (f ES'.a₆ * f ES.a₄) = f ES.a₆ * f ES'.a₄ := by
    have hden : E'.c₆ * E.c₄ ≠ 0 := mul_ne_zero hc₆' hc₄
    have hs' : s ^ 2 * (f E'.c₆ * f E.c₄) = f E.c₆ * f E'.c₄ := by
      rw [← map_mul, ← map_mul, hs, ← map_mul, div_mul_cancel₀ _ hden]
    have h41 : (41472 : K) ≠ 0 := by
      have := mul_ne_zero (pow_ne_zero 9 h2) (pow_ne_zero 4 h3); norm_num at this; exact this
    have h41L : (41472 : L) ≠ 0 := by rw [← map_ofNat f]; exact (map_ne_zero f).mpr h41
    have he₁ := congrArg f e₁; have he₂ := congrArg f e₂
    have he₃ := congrArg f e₃; have he₄ := congrArg f e₄
    simp only [map_mul, map_neg, map_ofNat] at he₁ he₂ he₃ he₄
    refine mul_right_cancel₀ h41L ?_
    linear_combination hs' + 864 * s^2 * f ES'.a₆ * he₁ - s^2 * f E.c₄ * he₄
      - 864 * f ES.a₆ * he₃ + f E'.c₄ * he₂

  have hu4 : s ^ 4 * f ES'.a₄ = f ES.a₄ := by
    have hrelL := congrArg f hrel
    simp only [map_mul, map_pow] at hrelL
    refine mul_right_cancel₀ (pow_ne_zero 2 (mul_ne_zero ((map_ne_zero f).mpr ha₆s')
      ((map_ne_zero f).mpr ha₄s))) ?_
    linear_combination (f ES'.a₄ * (s^2 * f ES'.a₆ * f ES.a₄ + f ES.a₆ * f ES'.a₄)) * hsA - hrelL
  have hu6 : s ^ 6 * f ES'.a₆ = f ES.a₆ := by
    refine mul_right_cancel₀ (mul_ne_zero ((map_ne_zero f).mpr ha₄s')
      ((map_ne_zero f).mpr ha₄s)) ?_
    linear_combination (s^2 * f ES'.a₆ * f ES.a₄) * hu4 + f ES.a₄ * hsA

  have hmid : (⟨Units.mk0 s hs0, 0, 0, 0⟩ : VariableChange L) • ES.map f = ES'.map f := by
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
    · simp only [variableChange_a₁, map_a₁, ES.a₁_of_isShortNF, ES'.a₁_of_isShortNF, map_zero]
      ring
    · simp only [variableChange_a₂, map_a₂, map_a₁, ES.a₂_of_isShortNF, ES'.a₂_of_isShortNF,
        ES.a₁_of_isShortNF, map_zero]
      ring
    · simp only [variableChange_a₃, map_a₃, map_a₁, ES.a₃_of_isShortNF, ES'.a₃_of_isShortNF,
        ES.a₁_of_isShortNF, map_zero]
      ring
    · simp only [variableChange_a₄, map_a₄, map_a₃, map_a₂, map_a₁, ES.a₃_of_isShortNF,
        ES.a₂_of_isShortNF, ES.a₁_of_isShortNF, map_zero, Units.val_inv_eq_inv_val,
        Units.val_mk0, mul_zero, zero_mul, sub_zero, add_zero, zero_add]
      ring_nf
      rw [← hu4, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hs0, one_pow, one_mul]
    · simp only [variableChange_a₆, map_a₆, map_a₄, map_a₃, map_a₂, map_a₁, ES.a₃_of_isShortNF,
        ES.a₂_of_isShortNF, ES.a₁_of_isShortNF, map_zero, Units.val_inv_eq_inv_val,
        Units.val_mk0, mul_zero, zero_mul, sub_zero, add_zero, zero_add]
      ring_nf
      rw [← hu6, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hs0, one_pow, one_mul]

  calc ((E'.toShortNF⁻¹).map f * (⟨Units.mk0 s hs0,0,0,0⟩:VariableChange L) * (E.toShortNF).map f)
        • E.map f
      = (E'.toShortNF⁻¹).map f • ((⟨Units.mk0 s hs0,0,0,0⟩:VariableChange L)
          • ((E.toShortNF).map f • E.map f)) := by rw [mul_smul, mul_smul]
    _ = (E'.toShortNF⁻¹).map f • ((⟨Units.mk0 s hs0,0,0,0⟩:VariableChange L) • ES.map f) := by
        rw [show (E.toShortNF.map f • E.map f : WeierstrassCurve L) = ES.map f from
          (map_variableChange _ _ _).trans (congrArg (·.map f) hES.symm)]
    _ = (E'.toShortNF⁻¹).map f • ES'.map f := by rw [hmid]
    _ = (E'.toShortNF⁻¹ • ES').map f := by rw [map_variableChange]
    _ = E'.map f := by rw [hES', inv_smul_smul]

end WeierstrassCurve

end S_WeierstrassCurve_exists_variableChange_map_of_j_eq_of_sq_factored
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_map_of_j_eq_of_sq_factored (solution)
