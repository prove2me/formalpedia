-- Prove2me | solution 1 for ProbabilityTheory.isPiSystem_prmEvalPiSystem
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T15:01:39.595996+00:00
-- url     : https://prove2.me/submissions/27dc991d-69a1-4792-81df-fba5e547fd0c

import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {m : Measure E}

/-- Finite intersections of Poisson-evaluation events form a pi-system. -/
theorem solution {R : Set E} : IsPiSystem (prmEvalPiSystem K X m R) := by
  unfold prmEvalPiSystem
  exact isPiSystem_piiUnionInter _
    (fun B : prmEvalIndex m R =>
      @MeasurableSpace.isPiSystem_measurableSet Ω
        (MeasurableSpace.comap
          (fun ω => poissonRandomMeasure K X ω B.1)
          inferInstance))
    Set.univ
