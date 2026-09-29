-- Prove2me | solution 1 for azuma_hoeffding_two_sided
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T23:13:43.4711+00:00
-- url     : https://prove2.me/submissions/d335c37f-515a-405f-8546-f422b4da309d

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {μ : Measure Ω}
    {Y : ℕ → Ω → ℝ} {cY : ℕ → ℝ≥0} {ℱ : Filtration ℕ mΩ}
    [IsZeroOrProbabilityMeasure μ] [IsFiniteMeasure μ]
    (h_adapted : StronglyAdapted ℱ Y) (h0 : HasSubgaussianMGF (Y 0) (cY 0) μ) (n : ℕ)
    (h_subG : ∀ i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (cY (i + 1)) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i ∈ Finset.range n, Y i ω|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) := by
  -- right tail on Y
  have hR := measure_sum_ge_le_of_hasCondSubgaussianMGF h_adapted h0 n h_subG hε
  -- left tail on -Y
  have h_adapted' : StronglyAdapted ℱ (fun i => -(Y i)) := h_adapted.neg
  have h0' : HasSubgaussianMGF ((fun i => -(Y i)) 0) (cY 0) μ := h0.neg
  have h_subG' : ∀ i < n - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) ((fun i => -(Y i)) (i + 1)) (cY (i + 1)) μ := by
    intro i hi
    exact ((h_subG i hi : Kernel.HasSubgaussianMGF (Y (i + 1)) (cY (i + 1)) _ _).neg)
  have hL := measure_sum_ge_le_of_hasCondSubgaussianMGF h_adapted' h0' n h_subG' hε
  -- Set abbreviations
  set S : Ω → ℝ := fun ω => ∑ i ∈ Finset.range n, Y i ω with hS
  have hnegsum : ∀ ω, ∑ i ∈ Finset.range n, (-Y i) ω = -(S ω) := by
    intro ω; simp [hS, Finset.sum_neg_distrib]
  have hLset : {ω | ε ≤ ∑ i ∈ Finset.range n, (-Y i) ω} = {ω | ε ≤ -(S ω)} := by
    ext ω; simp only [Set.mem_setOf_eq, hnegsum]
  rw [hLset] at hL
  -- {ε ≤ |S|} ⊆ {ε ≤ S} ∪ {ε ≤ -S}
  have hsub : {ω | ε ≤ |S ω|} ⊆ {ω | ε ≤ S ω} ∪ {ω | ε ≤ -(S ω)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rcases abs_cases (S ω) with ⟨h1, _⟩ | ⟨h1, _⟩
    · left; rw [h1] at hω; exact hω
    · right; rw [h1] at hω; exact hω
  have hmono : μ.real {ω | ε ≤ |S ω|}
      ≤ μ.real ({ω | ε ≤ S ω} ∪ {ω | ε ≤ -(S ω)}) := by
    apply measureReal_mono hsub
  have hunion : μ.real ({ω | ε ≤ S ω} ∪ {ω | ε ≤ -(S ω)})
      ≤ μ.real {ω | ε ≤ S ω} + μ.real {ω | ε ≤ -(S ω)} :=
    measureReal_union_le _ _
  calc μ.real {ω | ε ≤ |S ω|}
      ≤ μ.real ({ω | ε ≤ S ω} ∪ {ω | ε ≤ -(S ω)}) := hmono
    _ ≤ μ.real {ω | ε ≤ S ω} + μ.real {ω | ε ≤ -(S ω)} := hunion
    _ ≤ Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i))
        + Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) := add_le_add hR hL
    _ = 2 * Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) := by ring
