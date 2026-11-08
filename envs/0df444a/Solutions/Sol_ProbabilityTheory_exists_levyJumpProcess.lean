-- Prove2me | solution 1 for ProbabilityTheory.exists_levyJumpProcess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:50:36.415056+00:00
-- url     : https://prove2.me/submissions/1dab2f17-cd9c-437d-8608-0f1a5c38d3c9

import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Theorems.Thm_ProbabilityTheory_exists_isLevyProcess_pureJump
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

/-! The source jump-law existence contract follows from a genuine Lévy process. -/
theorem solution (b : ℝ) {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (X : ℝ≥0 → Ω → ℝ),
      IsProbabilityMeasure μ ∧ HasIndependentIncrements X μ ∧ HasStationaryIncrements X μ ∧
        X 0 =ᵐ[μ] (fun _ => 0) ∧
        ∀ (t : ℝ≥0) (ξ : ℝ), charFun (μ.map (X t)) ξ
          = Complex.exp (((t : ℝ) : ℂ) * (LevyKhintchineTriple.mk b 0 ν hν).exponent ξ) := by
  obtain ⟨Ω, mΩ, μ, X, hprob, hlevy, _, hchar⟩ :=
    ProbabilityTheory.exists_isLevyProcess_pureJump b hν
  refine ⟨Ω, mΩ, μ, X, hprob, hlevy.indep_increments,
    hlevy.stationary_increments, ?_, hchar⟩
  change ∀ᵐ ω ∂μ, X 0 ω = 0
  simp [hlevy.start_zero]
