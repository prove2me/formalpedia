-- Prove2me | solution 1 for StochApproxDyn.Attractor.ae_limitSet_subset_attainableSet
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T01:29:55.242569+00:00
-- url     : https://prove2.me/submissions/9e475412-4bd2-4b64-b4e9-1e24899b71b3

import Mathlib
import Definitions.Def_StochApproxDyn_Attractor_Dynamics
import Definitions.Def_StochApproxDyn_Attractor_Process

open scoped NNReal ENNReal
open MeasureTheory

open NNReal ENNReal MeasureTheory StochApproxDyn.Attractor in
theorem solution {Ω M : Type*} {m0 : MeasurableSpace Ω}
    [MetricSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    (Φ : Flow ℝ≥0 M) (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0)
    (X : ℝ≥0 → Ω → M) (w : ℝ≥0 → ℝ≥0 → ℝ≥0 → ℝ≥0)
    (hX : SatisfiesStandingAssumption Φ P ℱ X w) :
    ∀ᵐ ω ∂P, StochApproxDyn.LimitSet.limitSet (fun t => X t ω) ⊆ attainableSet P X := by
  classical
  have : Countable (TopologicalSpace.countableBasis M) :=
    (TopologicalSpace.countable_countableBasis M).to_subtype
  have key : ∀ᵐ ω ∂P, ∀ i : TopologicalSpace.countableBasis M × ℕ,
      P {ω' | ∃ s : ℝ≥0, (i.2 : ℝ≥0) ≤ s ∧ X s ω' ∈ (i.1 : Set M)} = 0 →
        ω ∉ {ω' | ∃ s : ℝ≥0, (i.2 : ℝ≥0) ≤ s ∧ X s ω' ∈ (i.1 : Set M)} := by
    rw [ae_all_iff]
    intro i
    by_cases h : P {ω' | ∃ s : ℝ≥0, (i.2 : ℝ≥0) ≤ s ∧ X s ω' ∈ (i.1 : Set M)} = 0
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 h] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun ω h' => absurd h' h
  filter_upwards [key] with ω hω
  intro p hp t ht V hV hpV
  rw [pos_iff_ne_zero]
  intro h0
  obtain ⟨U, hUB, hpU, hUV⟩ :=
    (TopologicalSpace.isBasis_countableBasis M).exists_subset_of_mem_open hpV hV
  have hn : t ≤ ((⌈t⌉₊ : ℕ) : ℝ≥0) := Nat.le_ceil t
  have hnull : P {ω' | ∃ s : ℝ≥0, (((⌈t⌉₊ : ℕ)) : ℝ≥0) ≤ s ∧ X s ω' ∈ U} = 0 := by
    refine measure_mono_null ?_ h0
    rintro ω' ⟨s, hs, hsU⟩
    exact ⟨s, hn.trans hs, hUV hsU⟩
  apply hω (⟨U, hUB⟩, ⌈t⌉₊) hnull
  have hcl : p ∈ closure ((fun t => X t ω) '' Set.Ici ((⌈t⌉₊ : ℕ) : ℝ≥0)) := by
    have := hp
    simp only [StochApproxDyn.LimitSet.limitSet, Set.mem_iInter] at this
    exact this _
  obtain ⟨q, hqU, s, hs, rfl⟩ :=
    mem_closure_iff.1 hcl U ((TopologicalSpace.isBasis_countableBasis M).isOpen hUB) hpU
  exact ⟨s, hs, hqU⟩
