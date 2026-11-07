-- Prove2me | solution 1 for StochIneqPO.Comparison.corollary1_ii
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T17:37:14.579145+00:00
-- url     : https://prove2.me/submissions/e26433ad-1592-4f31-b975-f347f2005849
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE
import Theorems.Thm_StochIneqPO_Comparison_comparison_theorem

open MeasureTheory ProbabilityTheory Finset StochIneqPO.Comparison

theorem solution {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E]
    [BorelSpace E] [PartialOrder E] [OrderClosedTopology E]
    (P₁ Q₁ : Measure E) [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    (p q : (n : ℕ) → Kernel (Π _ : Iic n, E) E)
    [∀ n, IsMarkovKernel (p n)] [∀ n, IsMarkovKernel (q n)]
    (hPQ : StochLE P₁ Q₁)
    (hpq : ∀ n, ∀ x y : Π _ : Iic n, E, x ≤ y → StochLE (p n x) (q n y))
    (A : Set E) (hA : MeasurableSet A) (hAup : IsUpperSet A) :
    (∀ m : ℕ, Kernel.trajMeasure (X := fun _ => E) P₁ p {x | ∃ i < m, x i ∈ A} ≤
        Kernel.trajMeasure (X := fun _ => E) Q₁ q {x | ∃ i < m, x i ∈ A}) ∧
      Kernel.trajMeasure (X := fun _ => E) P₁ p {x | ∃ i, x i ∈ A} ≤
        Kernel.trajMeasure (X := fun _ => E) Q₁ q {x | ∃ i, x i ∈ A} := by
  obtain ⟨Ω, mΩ, μ, hμ, X, Y, hX, hY, hlX, hlY, hle⟩ :=
    comparison_theorem (E := fun _ => E) P₁ Q₁ p q hPQ hpq
  have hXm : Measurable (fun ω n => X n ω) := measurable_pi_lambda _ hX
  have hYm : Measurable (fun ω n => Y n ω) := measurable_pi_lambda _ hY
  constructor
  · intro m
    have hS : MeasurableSet {x : ℕ → E | ∃ i < m, x i ∈ A} := by
      have : {x : ℕ → E | ∃ i < m, x i ∈ A} = ⋃ i ∈ Set.Iio m, {x | x i ∈ A} := by
        ext x; simp
      rw [this]
      exact MeasurableSet.biUnion (Set.to_countable _) fun i _ => measurable_pi_apply i hA
    rw [← hlX, ← hlY, Measure.map_apply hXm hS, Measure.map_apply hYm hS]
    apply measure_mono_ae
    filter_upwards [hle] with ω h hx
    obtain ⟨i, hi, hx⟩ := hx
    exact ⟨i, hi, hAup (h i) hx⟩
  · have hS : MeasurableSet {x : ℕ → E | ∃ i, x i ∈ A} := by
      have : {x : ℕ → E | ∃ i, x i ∈ A} = ⋃ i, {x | x i ∈ A} := by
        ext x; simp
      rw [this]
      exact MeasurableSet.iUnion fun i => measurable_pi_apply i hA
    rw [← hlX, ← hlY, Measure.map_apply hXm hS, Measure.map_apply hYm hS]
    apply measure_mono_ae
    filter_upwards [hle] with ω h hx
    obtain ⟨i, hx⟩ := hx
    exact ⟨i, hAup (h i) hx⟩
