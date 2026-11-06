-- Prove2me | solution 1 for ProbabilityTheory.exists_isPoissonPointFamily
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:29:15.366125+00:00
-- url     : https://prove2.me/submissions/c195630b-a05a-4efb-8588-77eed7ebf332

import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Order.Disjointed
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Function.Floor
import Definitions.Def_LeanLevy_Probability_Poisson

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem solution {E : Type} [MeasurableSpace E]
    (m : Measure E) [SigmaFinite m] [Nonempty E] :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E),
      IsProbabilityMeasure μ ∧ IsPoissonPointFamily K X m μ := by
  obtain ⟨Ω, mΩ, μ, Z, hmeas, hlaw, hindep, hμ⟩ :=
    exists_hasLaw_indepFun (pointFamilyIndexType E) (pointFamilyLaw m)
  refine ⟨Ω, mΩ, μ, fun k => Z (Sum.inl k),
    fun k n => Z (Sum.inr (k, n)), hμ, ?_⟩
  have hcomb : pointFamilyCombined
      (fun k => Z (Sum.inl k)) (fun k n => Z (Sum.inr (k, n))) = Z := by
    funext i ω
    rcases i with k | p
    · rfl
    · rfl
  exact
    { measurable_count := fun k => hmeas (Sum.inl k)
      measurable_point := fun k n => hmeas (Sum.inr (k, n))
      indep := by rw [hcomb]; exact hindep
      law_count := fun k => hlaw (Sum.inl k)
      law_point := fun k n => hlaw (Sum.inr (k, n)) }
