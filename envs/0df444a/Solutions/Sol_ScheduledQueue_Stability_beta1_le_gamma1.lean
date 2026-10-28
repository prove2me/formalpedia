-- Prove2me | solution 1 for ScheduledQueue.Stability.beta1_le_gamma1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T21:53:30.279762+00:00
-- url     : https://prove2.me/submissions/8453973c-2f49-45bf-9bd6-113c9049a56c

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

open ScheduledQueue.Stability in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledInput P ξ U) :
    (∀ ω, U ω ∈ Icc (0 : ℝ) 1 → ∀ s : ℝ, beta1 h ξ U s ω ≤ gamma1 h ξ ω) ∧
      ∫⁻ ω, (gamma1 h ξ ω : ℝ≥0∞) ∂P < ∞ := by
  refine ⟨?_, ?_⟩
  · intro ω hU s
    apply encard_le_encard
    rintro j ⟨hj1, hj2, -⟩
    refine ⟨hj1, ?_⟩
    simp only [revArrival] at hj2
    push_cast at hj2
    nlinarith [hU.2]
  · -- write Γ₁ as a sum of indicators
    set G : Ω → Set ℤ := fun ω => {j : ℤ | 1 ≤ j ∧ (j - 1) * h < -ξ (-j) ω}
    have hG : ∀ ω, (gamma1 h ξ ω : ℝ≥0∞) = ∑' j : ℤ, (G ω).indicator (fun _ => (1 : ℝ≥0∞)) j := by
      intro ω
      rw [← tsum_subtype (G ω) (fun _ => (1 : ℝ≥0∞)), ENNReal.tsum_set_one]
      rfl
    have hmeasj : ∀ j : ℤ, Measurable (fun ω => (G ω).indicator (fun _ => (1 : ℝ≥0∞)) j) := by
      intro j
      have : MeasurableSet {ω | 1 ≤ j ∧ (j - 1) * h < -ξ (-j) ω} := by
        by_cases hj : 1 ≤ j
        · simp only [hj, true_and]
          exact measurableSet_lt measurable_const (hin.measurable _).neg
        · simp [hj]
      have e : (fun ω => (G ω).indicator (fun _ => (1 : ℝ≥0∞)) j) =
          {ω | 1 ≤ j ∧ (j - 1) * h < -ξ (-j) ω}.indicator (fun _ => 1) := by
        ext ω; simp [G, Set.indicator]
      rw [e]; exact measurable_const.indicator this
    simp_rw [hG]
    rw [lintegral_tsum (fun j => (hmeasj j).aemeasurable)]
    -- reindex over ℕ
    have hsupp : (Function.support fun j : ℤ =>
        ∫⁻ ω, (G ω).indicator (fun _ => (1 : ℝ≥0∞)) j ∂P) ⊆
        Set.range (fun n : ℕ => (n : ℤ) + 1) := by
      intro j hj
      by_contra hcon
      apply hj
      have : ¬ 1 ≤ j := by
        intro h1; exact hcon ⟨(j - 1).toNat, by simp only; rw [Int.toNat_of_nonneg (by omega)]; ring⟩
      simp [G, this]
    rw [← (show Function.Injective (fun n : ℕ => (n : ℤ) + 1) from
      fun a b hab => by simpa using hab).tsum_eq hsupp]
    set X : Ω → ℝ := fun ω => max (-ξ 0 ω) 0 / h
    have hXint : Integrable X P := (hin.integrable.neg.pos_part).div_const h
    have hX0 : 0 ≤ X := fun ω => div_nonneg (le_max_right _ _) hh.le
    have key : ∀ n : ℕ, ∫⁻ ω, (G ω).indicator (fun _ => (1 : ℝ≥0∞)) ((n : ℤ) + 1) ∂P =
        P {ω | X ω ∈ Ioi (n : ℝ)} := by
      intro n
      have e : (fun ω => (G ω).indicator (fun _ => (1 : ℝ≥0∞)) ((n : ℤ) + 1)) =
          {ω | (n : ℝ) * h < -ξ (-((n : ℤ) + 1)) ω}.indicator (fun _ => 1) := by
        ext ω; simp [G, Set.indicator]
      have hm : MeasurableSet {ω | (n : ℝ) * h < -ξ (-((n : ℤ) + 1)) ω} :=
        measurableSet_lt measurable_const (hin.measurable _).neg
      rw [e, lintegral_indicator_const hm, one_mul]
      have hid := (hin.identDistrib (-((n : ℤ) + 1)))
      have h1 : {ω | (n : ℝ) * h < -ξ (-((n : ℤ) + 1)) ω} =
          ξ (-((n : ℤ) + 1)) ⁻¹' {x | (n : ℝ) * h < -x} := rfl
      have h2 : {ω | X ω ∈ Ioi (n : ℝ)} = ξ 0 ⁻¹' {x | (n : ℝ) * h < -x} := by
        ext ω
        simp only [X, mem_setOf_eq, mem_Ioi, mem_preimage, lt_div_iff₀ hh]
        constructor
        · intro hx
          rcases le_total (-ξ 0 ω) 0 with hle | hle
          · rw [max_eq_right hle] at hx
            exfalso; have : (0 : ℝ) ≤ n * h := by positivity
            linarith
          · rwa [max_eq_left hle] at hx
        · intro hx; exact lt_of_lt_of_le hx (le_max_left _ _)
      rw [h1, h2]
      exact hid.measure_mem_eq (measurableSet_lt measurable_const measurable_neg)
    simp_rw [key]
    let _ : MeasureSpace Ω := ⟨P⟩
    exact tsum_prob_mem_Ioi_lt_top hXint hX0
