-- Prove2me | solution 1 for WeierstrassCurve.exists_isUnit_mul_pow_eight_eq_of_charTwo
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/955daa9f-de20-5669-8866-5f4197288e4b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_isUnit_mul_pow_eight_eq_of_charTwo

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open WeierstrassCurve WeierstrassCurve.Affine

namespace P2MKcWildEight

variable {M : Type*} [Field M]

section Val

variable (A : ValuationSubring M)

lemma val_lt_one_of_z {t z : M} (ht : A.valuation t < 1) (hz : z ^ 4 = t * z + t) :
    A.valuation z < 1 := by
  by_contra h
  push Not at h

  have h1 : A.valuation (t * z + t) < A.valuation z := by
    apply Valuation.map_add_lt
    · rw [Valuation.map_mul]
      calc A.valuation t * A.valuation z < 1 * A.valuation z :=
            mul_lt_mul_of_pos_right ht (lt_of_lt_of_le zero_lt_one h)
        _ = A.valuation z := one_mul _
    · exact lt_of_lt_of_le ht h
  have h2 : A.valuation z ≤ A.valuation (z ^ 4) := by
    rw [Valuation.map_pow]
    calc A.valuation z = A.valuation z * 1 := (mul_one _).symm
      _ ≤ A.valuation z * A.valuation z ^ 3 :=
          mul_le_mul_right (one_le_pow₀ h) _
      _ = A.valuation z ^ 4 := (pow_succ' _ 3).symm
  rw [hz] at h2
  exact absurd (lt_of_le_of_lt h2 h1) (lt_irrefl _)

lemma val_eq_one_of_eta {z η : M} (hz : A.valuation z ≤ 1) (hη : η ^ 2 + z * η + 1 = 0) :
    A.valuation η = 1 := by
  rcases lt_trichotomy (A.valuation η) 1 with h | h | h
  ·
    exfalso
    have h1 : (1 : M) = -(η ^ 2 + z * η) := by linear_combination hη
    have h2 : A.valuation (η ^ 2 + z * η) < 1 := by
      apply Valuation.map_add_lt
      · rw [Valuation.map_pow]
        exact pow_lt_one₀ zero_le' h (by norm_num)
      · rw [Valuation.map_mul]
        calc A.valuation z * A.valuation η ≤ 1 * A.valuation η := mul_le_mul_left hz _
          _ = A.valuation η := one_mul _
          _ < 1 := h
    have h3 : A.valuation (1 : M) < 1 := by rw [h1, Valuation.map_neg]; exact h2
    rw [Valuation.map_one] at h3
    exact lt_irrefl _ h3
  · exact h
  ·
    exfalso
    have h1 : η ^ 2 = -(z * η + 1) := by linear_combination hη
    have hη0 : 0 < A.valuation η := lt_trans zero_lt_one h
    have h2 : A.valuation (z * η + 1) < A.valuation η ^ 2 := by
      apply Valuation.map_add_lt
      · rw [Valuation.map_mul]
        calc A.valuation z * A.valuation η ≤ 1 * A.valuation η := mul_le_mul_left hz _
          _ = A.valuation η := one_mul _
          _ = A.valuation η * 1 := (mul_one _).symm
          _ < A.valuation η * A.valuation η := mul_lt_mul_of_pos_left h hη0
          _ = A.valuation η ^ 2 := (sq _).symm
      · rw [Valuation.map_one]
        exact one_lt_pow₀ h (by norm_num)
    have h3 : A.valuation (η ^ 2) < A.valuation η ^ 2 := by
      rw [h1, Valuation.map_neg]; exact h2
    rw [Valuation.map_pow] at h3
    exact lt_irrefl _ h3

end Val

section Group

variable [CharP M 2] [DecidableEq M]

lemma psi3_of_order_three {t x₀ y₀ : M}
    (hP : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.Nonsingular x₀ y₀)
    (h3P : (3 : ℕ) • Point.some x₀ y₀ hP = 0) :
    t * x₀ ≠ 0 ∧ x₀ ^ 4 + t ^ 2 * x₀ ^ 3 + t ^ 7 = 0 ∧ y₀ ^ 2 + t * x₀ * y₀ = x₀ ^ 3 + t ^ 5 := by
  have h2 : (2 : M) = 0 := CharP.cast_eq_zero M 2
  have heq : y₀ ^ 2 + t * x₀ * y₀ = x₀ ^ 3 + t ^ 5 := by
    have h := (equation_iff x₀ y₀).mp hP.1
    have e1 : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.a₁ = t := rfl
    have e2 : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.a₂ = 0 := rfl
    have e3 : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.a₃ = 0 := rfl
    have e4 : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.a₄ = 0 := rfl
    have e6 : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.a₆ = t ^ 5 := rfl
    rw [e1, e2, e3, e4, e6] at h
    linear_combination h

  have h3 : Point.some x₀ y₀ hP + Point.some x₀ y₀ hP + Point.some x₀ y₀ hP = 0 := by
    rw [← h3P, show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul]
  have h2P : Point.some x₀ y₀ hP + Point.some x₀ y₀ hP = -Point.some x₀ y₀ hP :=
    eq_neg_of_add_eq_zero_left h3
  have hnegY : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.negY x₀ y₀ = -y₀ - t * x₀ := by
    rw [Affine.negY]
    show -y₀ - t * x₀ - 0 = -y₀ - t * x₀
    rw [sub_zero]

  have hy : y₀ ≠ (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.negY x₀ y₀ := by
    intro hy
    have h0 : Point.some x₀ y₀ hP + Point.some x₀ y₀ hP = 0 := Point.add_self_of_Y_eq hy
    rw [h0] at h2P
    exact Point.some_ne_zero _ (neg_eq_zero.mp h2P.symm)
  have hD : y₀ - (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.negY x₀ y₀ = t * x₀ := by
    rw [hnegY]; linear_combination y₀ * h2
  have htx : t * x₀ ≠ 0 := by rw [← hD]; exact sub_ne_zero.mpr hy

  rw [Point.add_self_of_Y_ne hy, Affine.Point.neg_some] at h2P
  have hX := (Point.some.inj h2P).1
  set L := (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.slope x₀ x₀ y₀ y₀ with hL
  have hLD : L * (t * x₀) = 3 * x₀ ^ 2 - t * y₀ := by
    rw [hL, Affine.slope_of_Y_ne rfl hy, hD]
    have : (3 * x₀ ^ 2 + 2 * (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.a₂ * x₀ +
        (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.a₄ -
        (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.a₁ * y₀) = 3 * x₀ ^ 2 - t * y₀ := by
      show 3 * x₀ ^ 2 + 2 * 0 * x₀ + 0 - t * y₀ = 3 * x₀ ^ 2 - t * y₀
      ring
    rw [this, div_mul_cancel₀ _ htx]
  have hX' : L ^ 2 + t * L - 2 * x₀ = x₀ := by
    have h := hX
    rw [Affine.addX] at h
    have e1 : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.a₁ = t := rfl
    have e2 : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.a₂ = 0 := rfl
    rw [e1, e2] at h
    linear_combination h
  refine ⟨htx, ?_, heq⟩

  have key : (L * (t * x₀)) ^ 2 + t * (t * x₀) * (L * (t * x₀)) - 2 * x₀ * (t * x₀) ^ 2 =
      x₀ * (t * x₀) ^ 2 := by
    have := congrArg (fun w => w * (t * x₀) ^ 2) hX'
    linear_combination this
  rw [hLD] at key

  linear_combination key - t ^ 2 * heq +
    (4 * x₀ ^ 4 - 3 * t * x₀ ^ 2 * y₀ + t ^ 2 * x₀ ^ 3 - t ^ 3 * x₀ * y₀ - t ^ 2 * x₀ ^ 3
      + 2 * x₀ * t ^ 3 * y₀ + 6 * x₀ ^ 2 * t * y₀ - 8 * x₀ ^ 4) * h2

end Group

theorem main [CharP M 2] [DecidableEq M] (A : ValuationSubring M)
    {t : M} (ht : t ∈ A) (htu : ¬ IsUnit (⟨t, ht⟩ : A)) (ht0 : t ≠ 0)
    {x₀ y₀ : M} (hP : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.Nonsingular x₀ y₀)
    (h3P : (3 : ℕ) • Point.some x₀ y₀ hP = 0) :
    ∃ (μ : M) (u : A), IsUnit u ∧ t = u * μ ^ 8 := by
  have h2 : (2 : M) = 0 := CharP.cast_eq_zero M 2
  obtain ⟨htx, hpsi, heq⟩ := psi3_of_order_three hP h3P
  have hx0 : x₀ ≠ 0 := fun h => htx (by rw [h, mul_zero])

  have hvt : A.valuation t < 1 := by
    have : (⟨t, ht⟩ : A) ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr htu
    exact (A.valuation_lt_one_iff ⟨t, ht⟩).mp this

  set z : M := t ^ 2 / x₀ with hz_def
  set η : M := t * y₀ / x₀ ^ 2 with hη_def
  have hzx : z * x₀ = t ^ 2 := by rw [hz_def]; exact div_mul_cancel₀ _ hx0
  have hηx : η * x₀ ^ 2 = t * y₀ := by rw [hη_def]; exact div_mul_cancel₀ _ (pow_ne_zero 2 hx0)
  have hz : z ^ 4 = t * z + t := by
    apply mul_right_cancel₀ (pow_ne_zero 4 hx0)
    linear_combination (z ^ 3 * x₀ ^ 3 + t ^ 2 * z ^ 2 * x₀ ^ 2 + t ^ 4 * z * x₀ + t ^ 6 - t * x₀ ^ 3) * hzx
      - t * hpsi + t ^ 8 * h2
  have hη : η ^ 2 + z * η + 1 = 0 := by
    have h1 : (η ^ 2 + z * η + 1) * x₀ ^ 4 = 0 := by
      linear_combination (η * x₀ ^ 2 + t * y₀ + x₀ * t ^ 2) * hηx + (x₀ * η * x₀ ^ 2) * hzx +
        hpsi + t ^ 2 * heq
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h (pow_ne_zero 4 hx0)
  have hvz : A.valuation z < 1 := val_lt_one_of_z A hvt hz
  have hvη : A.valuation η = 1 := val_eq_one_of_eta A hvz.le hη
  have hzA : z ∈ A := (A.valuation_le_one_iff z).mp hvz.le
  have hηA : η ∈ A := (A.valuation_le_one_iff η).mp hvη.le

  have hv1z : A.valuation (1 + z) = 1 := by
    rw [Valuation.map_add_eq_of_lt_left]
    · exact Valuation.map_one _
    · rw [Valuation.map_one]; exact hvz
  have h1zA : 1 + z ∈ A := add_mem A.one_mem hzA
  let w : A := ⟨(1 + z) * η ^ 4, mul_mem h1zA (pow_mem hηA 4)⟩
  have hw : IsUnit w := by
    rw [A.valuation_eq_one_iff]
    show A.valuation ((1 + z) * η ^ 4) = 1
    rw [Valuation.map_mul, Valuation.map_pow, hv1z, hvη, one_pow, one_mul]

  refine ⟨η + 1, (hw.unit⁻¹ : Aˣ), (hw.unit⁻¹).isUnit, ?_⟩
  have hμ2 : (η + 1) ^ 2 = z * η := by
    linear_combination hη + (η - z * η) * h2
  have hμ8 : (η + 1) ^ 8 = t * ((1 + z) * η ^ 4) := by
    calc (η + 1) ^ 8 = ((η + 1) ^ 2) ^ 4 := by ring
      _ = z ^ 4 * η ^ 4 := by rw [hμ2]; ring
      _ = t * ((1 + z) * η ^ 4) := by rw [hz]; ring
  have hwM : ((hw.unit⁻¹ : Aˣ) : A) * w = 1 := hw.unit.inv_mul
  have hwM' : (((hw.unit⁻¹ : Aˣ) : A) : M) * ((1 + z) * η ^ 4) = 1 :=
    congrArg Subtype.val hwM
  calc t = t * ((((hw.unit⁻¹ : Aˣ) : A) : M) * ((1 + z) * η ^ 4)) := by rw [hwM', mul_one]
    _ = (((hw.unit⁻¹ : Aˣ) : A) : M) * (t * ((1 + z) * η ^ 4)) := by ring
    _ = (((hw.unit⁻¹ : Aˣ) : A) : M) * (η + 1) ^ 8 := by rw [hμ8]

end P2MKcWildEight

universe u in
theorem solution
    {M : Type u} [Field M] [CharP M 2] [DecidableEq M] (A : ValuationSubring M)
    {t : M} (ht : t ∈ A) (htu : ¬ IsUnit (⟨t, ht⟩ : A)) (ht0 : t ≠ 0)
    {x₀ y₀ : M} (hP : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.Nonsingular x₀ y₀)
    (h3P : (3 : ℕ) • Point.some x₀ y₀ hP = 0) :
    ∃ (μ : M) (u : A), IsUnit u ∧ t = u * μ ^ 8 :=
  P2MKcWildEight.main A ht htu ht0 hP h3P

end S_WeierstrassCurve_exists_isUnit_mul_pow_eight_eq_of_charTwo
end P2MW
export P2MW.S_WeierstrassCurve_exists_isUnit_mul_pow_eight_eq_of_charTwo (solution)
