-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.proposition_2_10
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:19:54.736172+00:00
-- url     : https://prove2.me/submissions/6ee55917-768f-403b-bee2-8c074f510b6c

import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology

theorem solution {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [PolishSpace X] [BorelSpace X] (μ : ℕ → ProbabilityMeasure X)
    (htight : IsTightMeasureSet {((μ n : ProbabilityMeasure X) : Measure X) | n : ℕ}) :
    ∃ ν : ProbabilityMeasure X, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable X
  have hc : IsCompact (closure (range μ)) :=
    isCompact_closure_of_isTightMeasureSet (by simpa using htight)
  obtain ⟨ν,hν,φ,hφ,hlim⟩ := hc.tendsto_subseq (fun n => subset_closure ⟨n,rfl⟩)
  exact ⟨ν,φ,hφ,hlim⟩
