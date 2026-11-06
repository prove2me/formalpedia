-- Prove2me | solution 1 for ProbabilityTheory.prmFiltration_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:25:13.787484+00:00
-- url     : https://prove2.me/submissions/a4069be2-9482-41ec-9187-9c84d51480ea

import Definitions.Def_LeanLevy_RandomMeasure_PoissonMartingale
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {E : Type} [MeasurableSpace E] {m : Measure E} [SigmaFinite m]
  {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × E}
  {hK : ∀ k, Measurable (K k)} {hX : ∀ k n, Measurable (X k n)}
theorem solution (t : ℝ≥0) :
    prmFiltration K X m hK hX t
      = prmEvalSigma K X (volume.prod m) (Set.Iic (t : ℝ) ×ˢ Set.univ) := by
  rfl