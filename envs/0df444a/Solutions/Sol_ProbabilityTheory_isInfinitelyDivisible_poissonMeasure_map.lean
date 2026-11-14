-- Prove2me | solution 1 for ProbabilityTheory.isInfinitelyDivisible_poissonMeasure_map
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T20:23:56.10636+00:00
-- url     : https://prove2.me/submissions/c42182b6-ea26-4417-9c00-a98910fce36a

import Definitions.Def_LeanLevy_Levy_InfiniteDivisible
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Processes_PoissonProcess
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
import Definitions.Def_levy_foundations_iteratedConvolutionPower
import Theorems.Thm_levy_foundations_poissonLaw_infinitelyDivisible

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped NNReal ENNReal

theorem solution (r : ℝ≥0) :
    ProbabilityTheory.IsInfinitelyDivisible
      ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) := by
  have hpower (ν : Measure ℝ) (k : ℕ) :
      ν.iteratedConv k = LevyFoundations.iteratedConvolutionPower ν k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      change ν ∗ ν.iteratedConv k =
        ν ∗ LevyFoundations.iteratedConvolutionPower ν k
      exact congrArg (fun ρ : Measure ℝ => ν ∗ ρ) ih
  intro n hn
  obtain ⟨ν, hν, hconv⟩ := (levy_foundations_poissonLaw_infinitelyDivisible r) n hn
  exact ⟨ν, hν, hconv.trans (hpower ν n).symm⟩
