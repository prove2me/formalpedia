-- Prove2me | solution 1 for OpaquePricing.Dominance.equal_sorted_events
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T06:01:00.778007+00:00
-- url     : https://prove2.me/submissions/0874e4a4-e70a-4d94-9f57-39039b61ae21

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting

open MeasureTheory
open OpaquePricing.Dominance

theorem solution {N : ℕ} (μ : Measure (Fin N → ℝ))
    (hexch : Exchangeable μ) (σ τ : Equiv.Perm (Fin N)) :
    μ (sortedEvent σ) = μ (sortedEvent τ) := by
  have hmeas : ∀ τ : Equiv.Perm (Fin N), MeasurableSet (sortedEvent τ) := by
    intro τ
    have e : sortedEvent τ = ⋂ i, ⋂ j, {v : Fin N → ℝ | i ≤ j → v (τ j) ≤ v (τ i)} := by
      ext v; simp [sortedEvent]
    rw [e]
    refine MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j => ?_))
    by_cases hij : i ≤ j
    · simp only [hij, true_implies]
      exact measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _)
    · simp [hij]
  let ρ : Equiv.Perm (Fin N) := τ.symm.trans σ
  have hf : Measurable fun v : Fin N → ℝ => v ∘ ρ :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (ρ i))
  have hpre : sortedEvent σ = (fun v : Fin N → ℝ => v ∘ ρ) ⁻¹' sortedEvent τ := by
    ext v; simp [sortedEvent, ρ]
  rw [hpre, ← Measure.map_apply hf (hmeas τ), hexch ρ]
