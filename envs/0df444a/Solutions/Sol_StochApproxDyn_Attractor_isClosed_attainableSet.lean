-- Prove2me | solution 1 for StochApproxDyn.Attractor.isClosed_attainableSet
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T22:53:05.023114+00:00
-- url     : https://prove2.me/submissions/d835e61f-e737-4725-b090-ce9d9fbfcade

import Mathlib
import Definitions.Def_StochApproxDyn_Attractor_Dynamics
import Definitions.Def_StochApproxDyn_Attractor_Process

open scoped NNReal ENNReal
open MeasureTheory

/-! Lemma 7.1, first assertion (Benaïm 1999, p. 31): `Att(X)` is closed. -/

open MeasureTheory NNReal ENNReal StochApproxDyn.Attractor in
theorem solution {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M]
    [MeasurableSpace M] [BorelSpace M] (Φ : Flow ℝ≥0 M) (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 m0) (X : ℝ≥0 → Ω → M) (w : ℝ≥0 → ℝ≥0 → ℝ≥0 → ℝ≥0)
    (hX : SatisfiesStandingAssumption Φ P ℱ X w) :
    IsClosed (attainableSet P X) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro p hp
  have hp' : ¬ ∀ t : ℝ≥0, 0 < t → ∀ U : Set M, IsOpen U → p ∈ U →
      0 < P {ω | ∃ s : ℝ≥0, t ≤ s ∧ X s ω ∈ U} := hp
  push Not at hp'
  obtain ⟨t, ht, U, hU, hpU, hP⟩ := hp'
  refine ⟨U, fun q hq hqA => ?_, hU, hpU⟩
  have h1 : 0 < P {ω | ∃ s : ℝ≥0, t ≤ s ∧ X s ω ∈ U} := hqA t ht U hU hq
  exact (not_lt.mpr hP) h1
