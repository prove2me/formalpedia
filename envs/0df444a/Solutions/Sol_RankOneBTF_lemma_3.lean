-- Prove2me | solution 1 for RankOneBTF.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T22:05:11.06709+00:00
-- url     : https://prove2.me/submissions/279665e6-9d80-4670-8818-72307162c11b

import Mathlib

open MeasureTheory ProbabilityTheory

namespace Aux_RankOneBTF_l3

theorem key (E1 E2 t u v a b : ℝ) (hE1 : 0 < E1) (hE2 : 0 < E2) (ht : 0 < t)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u * v = t)
    (ha : a * (u + 2 * E2) = t) (hb : b * (v + 2 * E1) = t) :
    E2 * a + E1 * b + a * b ≤ t := by
  have hP : 0 < u + 2 * E2 := by linarith
  have hQ : 0 < v + 2 * E1 := by linarith
  have hPQ : 0 < (u + 2 * E2) * (v + 2 * E1) := mul_pos hP hQ
  have e : (E2 * a + E1 * b + a * b) * ((u + 2 * E2) * (v + 2 * E1)) =
      E2 * t * (v + 2 * E1) + E1 * t * (u + 2 * E2) + t * t := by
    linear_combination (E2 * (v + 2 * E1) + b * (v + 2 * E1)) * ha + (E1 * (u + 2 * E2) + t) * hb
  have e2 : (u + 2 * E2) * (v + 2 * E1) - E2 * (v + 2 * E1) - E1 * (u + 2 * E2) - t =
      E1 * u + E2 * v := by
    linear_combination huv
  have hnn : 0 ≤ t * (E1 * u + E2 * v) := by positivity
  have key : (E2 * a + E1 * b + a * b) * ((u + 2 * E2) * (v + 2 * E1)) ≤
      t * ((u + 2 * E2) * (v + 2 * E1)) := by
    rw [e]
    nlinarith
  exact le_of_mul_le_mul_right key hPQ

end Aux_RankOneBTF_l3

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X₁ X₂ : Ω → ℝ) (hm₁ : Measurable X₁) (hm₂ : Measurable X₂)
    (hi₁ : Integrable X₁ μ) (hi₂ : Integrable X₂ μ)
    (hnn₁ : ∀ ω, 0 ≤ X₁ ω) (hnn₂ : ∀ ω, 0 ≤ X₂ ω) (hind : IndepFun X₁ X₂ μ)
    (hE₁ : 0 < ∫ ω, X₁ ω ∂μ) (hE₂ : 0 < ∫ ω, X₂ ω ∂μ) (f₁ f₂ : ℝ → ℝ)
    (h₁ : ∀ t, 0 < t → μ.real {ω | t ≤ |X₁ ω - ∫ ω', X₁ ω' ∂μ|} ≤ f₁ t)
    (h₂ : ∀ t, 0 < t → μ.real {ω | t ≤ |X₂ ω - ∫ ω', X₂ ω' ∂μ|} ≤ f₂ t)
    (t : ℝ) (ht : 0 < t) :
    μ.real {ω | t ≤ |X₁ ω * X₂ ω - ∫ ω', X₁ ω' * X₂ ω' ∂μ|} ≤
      f₁ (t / (Real.sqrt (t * (∫ ω, X₂ ω ∂μ) / ∫ ω, X₁ ω ∂μ) + 2 * ∫ ω, X₂ ω ∂μ)) +
      f₂ (t / (Real.sqrt (t * (∫ ω, X₁ ω ∂μ) / ∫ ω, X₂ ω ∂μ) + 2 * ∫ ω, X₁ ω ∂μ)) := by
  have hprod : ∫ ω', X₁ ω' * X₂ ω' ∂μ = (∫ ω, X₁ ω ∂μ) * ∫ ω, X₂ ω ∂μ :=
    hind.integral_fun_mul_eq_mul_integral hm₁.aestronglyMeasurable hm₂.aestronglyMeasurable
  rw [hprod]
  generalize hE1d : (∫ ω, X₁ ω ∂μ) = E1 at hE₁ h₁ ⊢
  generalize hE2d : (∫ ω, X₂ ω ∂μ) = E2 at hE₂ h₂ ⊢
  have hE1ne : E1 ≠ 0 := hE₁.ne'
  have hE2ne : E2 ≠ 0 := hE₂.ne'
  obtain ⟨u, hu⟩ : ∃ u, u = Real.sqrt (t * E2 / E1) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = Real.sqrt (t * E1 / E2) := ⟨_, rfl⟩
  rw [← hu, ← hv]
  have hu0 : 0 ≤ u := by rw [hu]; exact Real.sqrt_nonneg _
  have hv0 : 0 ≤ v := by rw [hv]; exact Real.sqrt_nonneg _
  have huv : u * v = t := by
    rw [hu, hv, ← Real.sqrt_mul (by positivity)]
    have h2 : t * E2 / E1 * (t * E1 / E2) = t ^ 2 := by
      field_simp <;> ring
    rw [h2, Real.sqrt_sq ht.le]
  have hP : 0 < u + 2 * E2 := by linarith
  have hQ : 0 < v + 2 * E1 := by linarith
  obtain ⟨a, had⟩ : ∃ a, a = t / (u + 2 * E2) := ⟨_, rfl⟩
  obtain ⟨b, hbd⟩ : ∃ b, b = t / (v + 2 * E1) := ⟨_, rfl⟩
  rw [← had, ← hbd]
  have ha0 : 0 < a := by rw [had]; positivity
  have hb0 : 0 < b := by rw [hbd]; positivity
  have ha : a * (u + 2 * E2) = t := by rw [had]; exact div_mul_cancel₀ t hP.ne'
  have hb : b * (v + 2 * E1) = t := by rw [hbd]; exact div_mul_cancel₀ t hQ.ne'
  have hk := Aux_RankOneBTF_l3.key E1 E2 t u v a b hE₁ hE₂ ht hu0 hv0 huv ha hb
  have hsub : {ω | t ≤ |X₁ ω * X₂ ω - E1 * E2|} ⊆
      {ω | a ≤ |X₁ ω - E1|} ∪ {ω | b ≤ |X₂ ω - E2|} := by
    intro ω hω
    by_contra hn
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hn hω
    obtain ⟨h1, h2⟩ := hn
    have t1 : |(X₁ ω - E1) * (X₂ ω - E2) + (E2 * (X₁ ω - E1) + E1 * (X₂ ω - E2))| ≤
        |(X₁ ω - E1) * (X₂ ω - E2)| + (|E2 * (X₁ ω - E1)| + |E1 * (X₂ ω - E2)|) :=
      (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hE₁, abs_of_pos hE₂] at t1
    have heq : X₁ ω * X₂ ω - E1 * E2 =
        (X₁ ω - E1) * (X₂ ω - E2) + (E2 * (X₁ ω - E1) + E1 * (X₂ ω - E2)) := by ring
    rw [heq] at hω
    have hp : |X₁ ω - E1| * |X₂ ω - E2| ≤ a * b :=
      mul_le_mul h1.le h2.le (abs_nonneg _) ha0.le
    have q1 : E2 * |X₁ ω - E1| < E2 * a := mul_lt_mul_of_pos_left h1 hE₂
    have q2 : E1 * |X₂ ω - E2| < E1 * b := mul_lt_mul_of_pos_left h2 hE₁
    linarith
  calc μ.real {ω | t ≤ |X₁ ω * X₂ ω - E1 * E2|}
      ≤ μ.real ({ω | a ≤ |X₁ ω - E1|} ∪ {ω | b ≤ |X₂ ω - E2|}) :=
        measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ μ.real {ω | a ≤ |X₁ ω - E1|} + μ.real {ω | b ≤ |X₂ ω - E2|} :=
        measureReal_union_le _ _
    _ ≤ f₁ a + f₂ b := add_le_add (h₁ a ha0) (h₂ b hb0)
