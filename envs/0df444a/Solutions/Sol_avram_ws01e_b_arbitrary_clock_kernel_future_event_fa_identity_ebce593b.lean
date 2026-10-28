-- Prove2me | solution 1 for avram_ws01e_b_arbitrary_clock_kernel_future_event_fa_identity_ebce593b
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:43:41.447689+00:00
-- url     : https://prove2.me/submissions/a47c363c-1ca6-4624-9675-452a674c3a0d

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω Θ β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Θ] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (Y : Ω → β) (hY : Measurable Y)
    (hInd : IndepFun τ Y P)
    (K : ℝ≥0 → Θ → Prop)
    (hK : MeasurableSet {z : ℝ≥0 × Θ | K z.1 z.2})
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (hKernel : ∀ a : ℝ≥0, Q {η : Θ | K a η} = discount a)
    (B : Set β) (hB : MeasurableSet B) 
    (hr : (let reward : β → ℝ≥0∞ := B.indicator (fun _ => 1); Measurable reward))
    (hF : (let reward : β → ℝ≥0∞ := B.indicator (fun _ => 1); Measurable (fun z : Ω × Θ => (τ z.1, z.2))))
    (hs0 : (let reward : β → ℝ≥0∞ := B.indicator (fun _ => 1); MeasurableSet
      {z : Ω × Θ | K (τ z.1) z.2}))
    (hs : (let reward : β → ℝ≥0∞ := B.indicator (fun _ => 1); MeasurableSet
      {z : Ω × Θ | K (τ z.1) z.2 ∧ Y z.1 ∈ B}))
    : (let reward : β → ℝ≥0∞ := B.indicator (fun _ => 1); (∀ (ω : Ω), Q (Prod.mk ω ⁻¹'
        {z : Ω × Θ | K (τ z.1) z.2 ∧ Y z.1 ∈ B}) =
      discount (τ ω) * reward (Y ω))) := by
  intro reward ω
  by_cases hY' : Y ω ∈ B
  · have : Prod.mk ω ⁻¹' {z : Ω × Θ | K (τ z.1) z.2 ∧ Y z.1 ∈ B} = {η | K (τ ω) η} := by
      ext η; simp [hY']
    rw [this, hKernel]
    simp [reward, hY']
  · have : Prod.mk ω ⁻¹' {z : Ω × Θ | K (τ z.1) z.2 ∧ Y z.1 ∈ B} = ∅ := by
      ext η; simp [hY']
    rw [this, measure_empty]
    simp [reward, hY']
