-- Prove2me | solution 1 for ProbabilityTheory.measureReal_count_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:31:12.33454+00:00
-- url     : https://prove2.me/submissions/425ac278-9ed0-4513-a573-4b2fea60f535

import Mathlib.Probability.Distributions.Poisson.Basic
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal

theorem solution
    {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {μ : Measure Ω} {k : ℕ}
    (hd : IsPoissonPointFamily K X m μ) (j : ℕ) :
    μ.real {ω | K k ω = j} =
      (poissonMeasure (m (prmPiece m k)).toNNReal).real {j} := by
  have h1 : μ {ω | K k ω = j} =
      poissonMeasure (m (prmPiece m k)).toNNReal {j} := by
    rw [show {ω | K k ω = j} = K k ⁻¹' {j} from rfl,
      ← Measure.map_apply (hd.measurable_count k) (measurableSet_singleton j),
      (hd.law_count k).map_eq]
  rw [measureReal_def, h1, ← measureReal_def]
