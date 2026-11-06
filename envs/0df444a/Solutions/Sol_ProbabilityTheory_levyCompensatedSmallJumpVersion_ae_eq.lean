-- Prove2me | solution 1 for ProbabilityTheory.levyCompensatedSmallJumpVersion_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:58:17.379531+00:00
-- url     : https://prove2.me/submissions/d8350432-b1dd-4662-8672-32b669edf547

import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_RandomMeasure_PoissonMartingale

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν]
  {μ : Measure Ω}

/-- Recover the a.e. agreement inherent in the source's measurable representative. -/
theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hν : IsLevyMeasure ν) (t : ℝ≥0) :
    levyCompensatedSmallJumpVersion hd hν t
      =ᵐ[μ] levyCompensatedSmallJump hd hν (t : ℝ) := by
  unfold levyCompensatedSmallJumpVersion
  exact (AEStronglyMeasurable.ae_eq_mk _).symm
