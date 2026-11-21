-- Prove2me | solution 1 for TradeAgentNV.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T03:04:31.122157+00:00
-- url     : https://prove2.me/submissions/33c9aaff-be5c-4938-b50d-ecf1be39a02b

import Mathlib

open MeasureTheory

theorem solution
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → ℝ) (hU : Measurable U)
    (hU01 : ∀ᵐ ω ∂P, U ω ∈ Set.Icc (0 : ℝ) 1) (hcont : ∀ x : ℝ, P {ω | U ω = x} = 0)
    (hEU1 : ∫ ω, U ω ∂P < 1) :
    ∀ s : ℝ, 0 < s → s < 1 → s < (∫ ω, min (U ω) s ∂P) / ∫ ω, U ω ∂P := by
  have hUint : Integrable U P := by
    refine Integrable.of_bound hU.aestronglyMeasurable 1 ?_
    filter_upwards [hU01] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
    exact hω.2
  have hEUpos : 0 < ∫ ω, U ω ∂P := by
    have hnonneg : 0 ≤ᵐ[P] U := by
      filter_upwards [hU01] with ω hω
      exact hω.1
    rw [integral_pos_iff_support_of_nonneg_ae hnonneg hUint]
    have hsupp : Function.support U = {ω | U ω = 0}ᶜ := by
      ext ω
      simp [Function.mem_support]
    rw [hsupp]
    have hmeas : MeasurableSet {ω | U ω = 0} := hU (measurableSet_singleton 0)
    have h0 : P {ω | U ω = 0} = 0 := hcont 0
    have hcompl : P {ω | U ω = 0}ᶜ = 1 := by
      rw [measure_compl hmeas (measure_ne_top _ _), h0]
      simp
    rw [hcompl]
    norm_num
  intro s hs0 hs1
  have hmin_id : ∀ ω, min (U ω) s = U ω - max (U ω - s) 0 := by
    intro ω
    rcases le_total s (U ω) with h | h
    · rw [min_eq_right h, max_eq_left (by linarith : (0 : ℝ) ≤ U ω - s)]
      ring
    · rw [min_eq_left h, max_eq_right (by linarith : U ω - s ≤ 0)]
      ring
  have hmaxint : Integrable (fun ω => max (U ω - s) 0) P := by
    have hmeas : Measurable (fun ω => max (U ω - s) 0) :=
      (hU.sub measurable_const).max measurable_const
    refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
    filter_upwards [hU01] with ω hω
    have h1 : 0 ≤ max (U ω - s) 0 := le_max_right _ _
    have h3 : max (U ω - s) 0 ≤ 1 := max_le (by linarith [hω.2]) zero_le_one
    rw [Real.norm_eq_abs, abs_of_nonneg h1]
    exact h3
  have hle_max : ∫ ω, max (U ω - s) 0 ∂P ≤ (1 - s) * ∫ ω, U ω ∂P := by
    have hpt : ∀ᵐ ω ∂P, max (U ω - s) 0 ≤ (1 - s) * U ω := by
      filter_upwards [hU01] with ω hω
      rcases le_total s (U ω) with h | h
      · rw [max_eq_left (by linarith : (0 : ℝ) ≤ U ω - s)]
        nlinarith [hω.2]
      · rw [max_eq_right (by linarith : U ω - s ≤ 0)]
        nlinarith [hω.1]
    calc ∫ ω, max (U ω - s) 0 ∂P ≤ ∫ ω, (1 - s) * U ω ∂P :=
          integral_mono_ae hmaxint (hUint.const_mul (1 - s)) hpt
      _ = (1 - s) * ∫ ω, U ω ∂P := by rw [integral_const_mul]
  by_cases hPs : P {ω | U ω > s} = 0
  · have hle : ∀ᵐ ω ∂P, U ω ≤ s := by
      have h := (measure_eq_zero_iff_ae_notMem).1 hPs
      simpa using h
    have hmin : ∫ ω, min (U ω) s ∂P = ∫ ω, U ω ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hle] with ω hω
      exact min_eq_left hω
    rw [hmin, div_self (ne_of_gt hEUpos)]
    exact hs1
  · have hPs' : 0 < P {ω | U ω > s} := pos_iff_ne_zero.mpr hPs
    have hlt1 : ∀ᵐ ω ∂P, U ω < 1 := by
      have hne : ∀ᵐ ω ∂P, U ω ≠ 1 := by
        have h := (measure_eq_zero_iff_ae_notMem).1 (hcont 1)
        simpa using h
      filter_upwards [hU01, hne] with ω hω hω1
      exact lt_of_le_of_ne hω.2 hω1
    have hset : {ω | U ω > s} =ᵐ[P] {ω | s < U ω ∧ U ω < 1} := by
      filter_upwards [hlt1] with ω hω
      change (U ω > s) = (s < U ω ∧ U ω < 1)
      exact propext ⟨fun h => ⟨h, hω⟩, fun h => h.1⟩
    have hPT : 0 < P {ω | s < U ω ∧ U ω < 1} := by
      rw [← measure_congr hset]
      exact hPs'
    let g : Ω → ℝ := fun ω => (1 - s) * U ω - max (U ω - s) 0
    have hgint : Integrable g P := (hUint.const_mul (1 - s)).sub hmaxint
    have hgnonneg : 0 ≤ᵐ[P] g := by
      filter_upwards [hU01] with ω hω
      show 0 ≤ (1 - s) * U ω - max (U ω - s) 0
      rcases le_total s (U ω) with h | h
      · rw [max_eq_left (by linarith : (0 : ℝ) ≤ U ω - s)]
        nlinarith [hω.2]
      · rw [max_eq_right (by linarith : U ω - s ≤ 0)]
        nlinarith [hω.1, hs1]
    have hgval : ∫ ω, g ω ∂P = (1 - s) * ∫ ω, U ω ∂P - ∫ ω, max (U ω - s) 0 ∂P := by
      show ∫ ω, ((1 - s) * U ω - max (U ω - s) 0) ∂P = _
      rw [integral_sub (hUint.const_mul (1 - s)) hmaxint, integral_const_mul]
    have hgpos : 0 < ∫ ω, g ω ∂P := by
      rw [integral_pos_iff_support_of_nonneg_ae hgnonneg hgint]
      have hsub : {ω | s < U ω ∧ U ω < 1} ⊆ Function.support g := by
        intro ω hω
        simp only [Set.mem_ofPred_eq] at hω
        show g ω ≠ 0
        apply ne_of_gt
        show 0 < (1 - s) * U ω - max (U ω - s) 0
        rw [max_eq_left (by linarith : (0 : ℝ) ≤ U ω - s)]
        nlinarith [hω.2, hs0]
      exact lt_of_lt_of_le hPT (measure_mono hsub)
    have hmaxlt : ∫ ω, max (U ω - s) 0 ∂P < (1 - s) * ∫ ω, U ω ∂P := by
      have := hgpos
      rw [hgval] at this
      linarith
    have hminval : ∫ ω, min (U ω) s ∂P = ∫ ω, U ω ∂P - ∫ ω, max (U ω - s) 0 ∂P := by
      have h1 : (fun ω => min (U ω) s) = fun ω => U ω - max (U ω - s) 0 := by
        funext ω
        exact hmin_id ω
      rw [h1, integral_sub hUint hmaxint]
    rw [lt_div_iff₀ hEUpos, hminval]
    nlinarith [hmaxlt]
