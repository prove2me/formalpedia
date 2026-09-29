-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_eq_legendreCurve_of_isUnit_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e6ff4ba4-9c31-5c80-ab57-44b067eea02b

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_eq_legendreCurve_of_isUnit_two

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open WeierstrassCurve

namespace P2MKcLegendreLocal

variable {M : Type*} [Field M]

section Val

variable (A : ValuationSubring M)

lemma val_lambda {j l : M} (hj : A.valuation j ≤ 1) (h2 : A.valuation (2 : M) = 1)
    (hjl : j * (l ^ 2 * (l - 1) ^ 2) = 256 * (l ^ 2 - l + 1) ^ 3) :
    A.valuation l = 1 ∧ A.valuation (l - 1) = 1 := by
  have h256 : A.valuation (256 : M) = 1 := by
    rw [show (256 : M) = 2 ^ 8 by norm_num, Valuation.map_pow, h2, one_pow]
  have hv1 : A.valuation (1 : M) = 1 := Valuation.map_one _
  have hvneg1 : A.valuation (-1 : M) = 1 := by rw [Valuation.map_neg, hv1]

  have hle : A.valuation l ≤ 1 := by
    by_contra h
    push Not at h
    have hl0 : 0 < A.valuation l := lt_trans zero_lt_one h
    have hlm1 : A.valuation (l - 1) = A.valuation l := by
      rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left]
      rwa [hvneg1]
    have hquad : A.valuation (l ^ 2 - l + 1) = A.valuation l ^ 2 := by
      have h1 : A.valuation (-l + 1) < A.valuation (l ^ 2) := by
        rw [Valuation.map_pow]
        refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
        · rw [Valuation.map_neg]
          calc A.valuation l = A.valuation l * 1 := (mul_one _).symm
            _ < A.valuation l * A.valuation l := mul_lt_mul_of_pos_left h hl0
            _ = A.valuation l ^ 2 := (sq _).symm
        · rw [hv1]; exact one_lt_pow₀ h (by norm_num)
      rw [show l ^ 2 - l + 1 = l ^ 2 + (-l + 1) by ring, A.valuation.map_add_eq_of_lt_left h1,
        Valuation.map_pow]
    have hL : A.valuation (j * (l ^ 2 * (l - 1) ^ 2)) ≤ A.valuation l ^ 4 := by
      rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, Valuation.map_pow, hlm1]
      calc A.valuation j * (A.valuation l ^ 2 * A.valuation l ^ 2)
          ≤ 1 * (A.valuation l ^ 2 * A.valuation l ^ 2) := mul_le_mul_left hj _
        _ = A.valuation l ^ 4 := by rw [one_mul, ← pow_add]
    have hR : A.valuation (256 * (l ^ 2 - l + 1) ^ 3) = A.valuation l ^ 6 := by
      rw [Valuation.map_mul, h256, one_mul, Valuation.map_pow, hquad, ← pow_mul]
    rw [hjl, hR] at hL
    have : A.valuation l ^ 4 < A.valuation l ^ 6 := pow_lt_pow_right₀ h (by norm_num)
    exact absurd (lt_of_le_of_lt hL this) (lt_irrefl _)
  have hle1 : A.valuation (l - 1) ≤ 1 := by
    rw [sub_eq_add_neg]
    exact le_trans (Valuation.map_add _ _ _) (max_le hle (le_of_eq hvneg1))

  have hl : A.valuation l = 1 := by
    rcases lt_or_eq_of_le hle with h | h
    · exfalso
      have hquad : A.valuation (l ^ 2 - l + 1) = 1 := by
        have h1 : A.valuation (l ^ 2 - l) < A.valuation (1 : M) := by
          rw [hv1, sub_eq_add_neg]
          refine Valuation.map_add_lt _ ?_ ?_
          · rw [Valuation.map_pow]; exact pow_lt_one₀ zero_le' h (by norm_num)
          · rw [Valuation.map_neg]; exact h
        rw [A.valuation.map_add_eq_of_lt_right h1, hv1]
      have hL : A.valuation (j * (l ^ 2 * (l - 1) ^ 2)) < 1 := by
        rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, Valuation.map_pow]
        calc A.valuation j * (A.valuation l ^ 2 * A.valuation (l - 1) ^ 2)
            ≤ 1 * (A.valuation l ^ 2 * 1) := by
              apply mul_le_mul' hj
              exact mul_le_mul_right (pow_le_one₀ zero_le' hle1) _
          _ = A.valuation l ^ 2 := by rw [one_mul, mul_one]
          _ < 1 := pow_lt_one₀ zero_le' h (by norm_num)
      have hR : A.valuation (256 * (l ^ 2 - l + 1) ^ 3) = 1 := by
        rw [Valuation.map_mul, h256, one_mul, Valuation.map_pow, hquad, one_pow]
      rw [hjl, hR] at hL
      exact lt_irrefl _ hL
    · exact h

  have hl1 : A.valuation (l - 1) = 1 := by
    rcases lt_or_eq_of_le hle1 with h | h
    · exfalso
      have hquad : A.valuation (l ^ 2 - l + 1) = 1 := by
        have h1 : A.valuation ((l - 1) ^ 2 + (l - 1)) < A.valuation (1 : M) := by
          rw [hv1]
          refine Valuation.map_add_lt _ ?_ h
          rw [Valuation.map_pow]; exact pow_lt_one₀ zero_le' h (by norm_num)
        rw [show l ^ 2 - l + 1 = ((l - 1) ^ 2 + (l - 1)) + 1 by ring,
          A.valuation.map_add_eq_of_lt_right h1, hv1]
      have hL : A.valuation (j * (l ^ 2 * (l - 1) ^ 2)) < 1 := by
        rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, Valuation.map_pow, hl, one_pow,
          one_mul]
        calc A.valuation j * A.valuation (l - 1) ^ 2 ≤ 1 * A.valuation (l - 1) ^ 2 :=
              mul_le_mul_left hj _
          _ = A.valuation (l - 1) ^ 2 := one_mul _
          _ < 1 := pow_lt_one₀ zero_le' h (by norm_num)
      have hR : A.valuation (256 * (l ^ 2 - l + 1) ^ 3) = 1 := by
        rw [Valuation.map_mul, h256, one_mul, Valuation.map_pow, hquad, one_pow]
      rw [hjl, hR] at hL
      exact lt_irrefl _ hL
    · exact h
  exact ⟨hl, hl1⟩

end Val

section Model

variable (E : WeierstrassCurve M) [E.IsElliptic]

lemma legendre_Δ {R : Type*} [CommRing R] (l : R) : (legendreCurve l).Δ = 16 * l ^ 2 * (l - 1) ^ 2 := by
  simp only [legendreCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

lemma legendre_c₄ {R : Type*} [CommRing R] (l : R) : (legendreCurve l).c₄ = 16 * (l ^ 2 - l + 1) := by
  simp only [legendreCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

lemma legendre_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (l : R) :
    (legendreCurve l).map φ = legendreCurve (φ l) := by
  simp only [legendreCurve, WeierstrassCurve.map]
  ext <;> simp

theorem variableChange_eq_legendre (h2 : (2 : M) ≠ 0)
    {e₁ e₂ e₃ w : M} (he : E.twoTorsionPolynomial.roots = {e₁, e₂, e₃}) (hw : w ^ 2 = e₂ - e₁)
    (hw0 : w ≠ 0) :
    (⟨Units.mk0 w hw0, e₁, -E.a₁ / 2, -(E.a₃ + e₁ * E.a₁) / 2⟩ : VariableChange M) • E =
      legendreCurve ((e₃ - e₁) / (e₂ - e₁)) := by

  have ha : E.twoTorsionPolynomial.a ≠ 0 := by
    show (4 : M) ≠ 0
    rw [show (4 : M) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hmap : Cubic.map (RingHom.id M) E.twoTorsionPolynomial = E.twoTorsionPolynomial := by
    cases hP : E.twoTorsionPolynomial; rfl
  have he' : (Cubic.map (RingHom.id M) E.twoTorsionPolynomial).roots = {e₁, e₂, e₃} := by
    rw [hmap]; exact he
  have hV1 := Cubic.b_eq_three_roots ha he'
  have hV2 := Cubic.c_eq_three_roots ha he'
  have hV3 := Cubic.d_eq_three_roots ha he'
  simp only [RingHom.id_apply, twoTorsionPolynomial] at hV1 hV2 hV3

  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hV1 hV2 hV3
  have hw2 : e₂ - e₁ ≠ 0 := by rw [← hw]; exact pow_ne_zero 2 hw0
  ext
  ·
    simp only [legendreCurve, variableChange_a₁, Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
    ring
  ·
    simp only [legendreCurve, variableChange_a₂, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [← hw]
    field_simp
    linear_combination hV1 + 4 * hw
  ·
    simp only [legendreCurve, variableChange_a₃, Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
    ring
  ·
    simp only [legendreCurve, variableChange_a₄, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [← hw]
    have hV2' : 2 * E.a₄ + E.a₁ * E.a₃ = 2 * (e₁ * e₂ + e₁ * e₃ + e₂ * e₃) := by
      apply mul_left_cancel₀ h2
      linear_combination hV2
    field_simp
    linear_combination hV2' + e₁ * hV1 + 2 * (e₁ - e₃) * hw
  ·
    simp only [legendreCurve, variableChange_a₆, Units.val_inv_eq_inv_val, Units.val_mk0]

    have hroot : 4 * e₁ ^ 3 + E.b₂ * e₁ ^ 2 + 2 * E.b₄ * e₁ + E.b₆ = 0 := by
      have hmem : e₁ ∈ E.twoTorsionPolynomial.roots := by rw [he]; simp
      have hne : E.twoTorsionPolynomial.toPoly ≠ 0 := Cubic.ne_zero_of_a_ne_zero ha
      have := (Cubic.mem_roots_iff hne e₁).mp hmem
      simpa [twoTorsionPolynomial] using this
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hroot
    field_simp
    linear_combination hroot

lemma j_legendre_mul (l : M) [(legendreCurve l).IsElliptic] :
    (legendreCurve l).j * (l ^ 2 * (l - 1) ^ 2) = 256 * (l ^ 2 - l + 1) ^ 3 := by
  have hjΔ : (legendreCurve l).j * (legendreCurve l).Δ = (legendreCurve l).c₄ ^ 3 := by
    rw [WeierstrassCurve.j, mul_comm, ← mul_assoc, ← coe_Δ', Units.mul_inv, one_mul]
  rw [legendre_Δ, legendre_c₄] at hjΔ
  have h16 : (16 : M) ≠ 0 := by
    intro h
    apply (legendreCurve l).isUnit_Δ.ne_zero
    rw [legendre_Δ, h]; ring
  apply mul_left_cancel₀ h16
  linear_combination hjΔ

lemma j_mul_of_legendre (h2 : (2 : M) ≠ 0)
    {e₁ e₂ e₃ w : M} (he : E.twoTorsionPolynomial.roots = {e₁, e₂, e₃}) (hw : w ^ 2 = e₂ - e₁)
    (hw0 : w ≠ 0) :
    E.j * (((e₃ - e₁) / (e₂ - e₁)) ^ 2 * ((e₃ - e₁) / (e₂ - e₁) - 1) ^ 2) =
      256 * (((e₃ - e₁) / (e₂ - e₁)) ^ 2 - (e₃ - e₁) / (e₂ - e₁) + 1) ^ 3 := by
  have hκ := variableChange_eq_legendre E h2 he hw hw0
  haveI : (legendreCurve ((e₃ - e₁) / (e₂ - e₁))).IsElliptic := by rw [← hκ]; infer_instance
  have hj : E.j = (legendreCurve ((e₃ - e₁) / (e₂ - e₁))).j := by
    have h1 := variableChange_j E
      (⟨Units.mk0 w hw0, e₁, -E.a₁ / 2, -(E.a₃ + e₁ * E.a₁) / 2⟩ : VariableChange M)
    have h2' : ∀ (V₁ V₂ : WeierstrassCurve M) [V₁.IsElliptic] [V₂.IsElliptic], V₁ = V₂ → V₁.j = V₂.j := by
      rintro V₁ V₂ _ _ rfl; rfl
    rw [← h1]
    exact h2' _ _ hκ
  rw [hj]
  exact j_legendre_mul _

end Model

theorem main (A : ValuationSubring M) (h2 : IsUnit (2 : A))
    (E : WeierstrassCurve M) [E.IsElliptic] (hj : E.j ∈ A)
    {e₁ e₂ e₃ w : M} (he : E.twoTorsionPolynomial.roots = {e₁, e₂, e₃}) (hw : w ^ 2 = e₂ - e₁) :
    ∃ (l : A) (κ : VariableChange M), IsUnit l ∧ IsUnit (1 - l) ∧
      IsUnit (legendreCurve l).Δ ∧ (l : M) = (e₃ - e₁) / (e₂ - e₁) ∧
      (κ.u : M) = w ∧ κ.r = e₁ ∧ κ.s = -E.a₁ / 2 ∧ κ.t = -(E.a₃ + e₁ * E.a₁) / 2 ∧
      κ • E = (legendreCurve l).map A.subtype := by
  have h2M : (2 : M) ≠ 0 := by
    have : ((2 : A) : M) ≠ 0 := fun h => h2.ne_zero (Subtype.ext h)
    exact this
  have h2v : A.valuation (2 : M) = 1 := by
    have := (A.valuation_eq_one_iff (2 : A)).mp h2
    exact this

  have ha : E.twoTorsionPolynomial.a ≠ 0 := by
    show (4 : M) ≠ 0
    rw [show (4 : M) = 2 * 2 by norm_num]; exact mul_ne_zero h2M h2M
  have hmap : Cubic.map (RingHom.id M) E.twoTorsionPolynomial = E.twoTorsionPolynomial := by
    cases hP : E.twoTorsionPolynomial; rfl
  have he' : (Cubic.map (RingHom.id M) E.twoTorsionPolynomial).roots = {e₁, e₂, e₃} := by
    rw [hmap]; exact he
  have hdisc : E.twoTorsionPolynomial.discr ≠ 0 :=
    E.twoTorsionPolynomial_discr_ne_zero (isUnit_iff_ne_zero.mpr h2M) E.isUnit_Δ
  obtain ⟨h12, h13, h23⟩ := (Cubic.discr_ne_zero_iff_roots_ne ha he').mp hdisc
  have hw2 : e₂ - e₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; exact hw2 (by rw [← hw]; ring)

  set l₀ : M := (e₃ - e₁) / (e₂ - e₁) with hl₀
  have hjl := j_mul_of_legendre E h2M he hw hw0
  obtain ⟨hvl, hvl1⟩ := val_lambda A ((A.valuation_le_one_iff _).mpr hj) h2v hjl
  have hlA : l₀ ∈ A := (A.valuation_le_one_iff _).mp hvl.le
  set l : A := ⟨l₀, hlA⟩ with hl
  have hlu : IsUnit l := (A.valuation_eq_one_iff l).mpr hvl
  have hl1u : IsUnit (1 - l) := by
    rw [A.valuation_eq_one_iff]
    show A.valuation ((1 : M) - l₀) = 1
    rw [← neg_sub, Valuation.map_neg]; exact hvl1
  refine ⟨l, ⟨Units.mk0 w hw0, e₁, -E.a₁ / 2, -(E.a₃ + e₁ * E.a₁) / 2⟩, hlu, hl1u, ?_, rfl,
    rfl, rfl, rfl, rfl, ?_⟩
  ·
    rw [legendre_Δ]
    have h16 : IsUnit (16 : A) := by
      rw [show (16 : A) = 2 ^ 4 by norm_num]; exact h2.pow 4
    have hlm1 : IsUnit (l - 1) := by
      rw [show l - 1 = -(1 - l) by ring]; exact hl1u.neg
    exact ((h16.mul (hlu.pow 2)).mul (hlm1.pow 2))
  · rw [legendre_map, variableChange_eq_legendre E h2M he hw hw0]
    rfl

end P2MKcLegendreLocal

universe u in
theorem solution
    {M : Type u} [Field M] (A : ValuationSubring M) (h2 : IsUnit (2 : A))
    (E : WeierstrassCurve M) [E.IsElliptic] (hj : E.j ∈ A)
    {e₁ e₂ e₃ w : M} (he : E.twoTorsionPolynomial.roots = {e₁, e₂, e₃}) (hw : w ^ 2 = e₂ - e₁) :
    ∃ (l : A) (κ : VariableChange M), IsUnit l ∧ IsUnit (1 - l) ∧
      IsUnit (legendreCurve l).Δ ∧ (l : M) = (e₃ - e₁) / (e₂ - e₁) ∧
      (κ.u : M) = w ∧ κ.r = e₁ ∧ κ.s = -E.a₁ / 2 ∧ κ.t = -(E.a₃ + e₁ * E.a₁) / 2 ∧
      κ • E = (legendreCurve l).map A.subtype :=
  P2MKcLegendreLocal.main A h2 E hj he hw

end S_WeierstrassCurve_exists_variableChange_eq_legendreCurve_of_isUnit_two
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_eq_legendreCurve_of_isUnit_two (solution)
