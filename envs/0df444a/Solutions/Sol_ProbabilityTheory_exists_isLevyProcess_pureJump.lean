-- Prove2me | solution 1 for ProbabilityTheory.exists_isLevyProcess_pureJump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:21:05.782332+00:00
-- url     : https://prove2.me/submissions/f159b064-4f36-4f07-8873-f4b14428be31

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
import Theorems.Thm_ProbabilityTheory_exists_isPoissonPointFamily
import Theorems.Thm_ProbabilityTheory_isLevyProcess_levyJumpPath
import Theorems.Thm_ProbabilityTheory_measurable_levyJumpPath
import Theorems.Thm_ProbabilityTheory_charFun_map_levyJumpPath
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_sigmaFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- Source-exact construction of a pure-jump process on a Poisson-point space. -/
theorem solution (b : ℝ) {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (X : ℝ≥0 → Ω → ℝ),
      IsProbabilityMeasure μ ∧ IsLevyProcess X μ ∧ (∀ t, Measurable (X t)) ∧
      ∀ (t : ℝ≥0) (ξ : ℝ), charFun (μ.map (X t)) ξ =
        Complex.exp (((t : ℝ) : ℂ) * (LevyKhintchineTriple.mk b 0 ν hν).exponent ξ) := by
  haveI := hν.sigmaFinite
  obtain ⟨Ω, mΩ, μ, K, X, hprob, hd⟩ :=
    exists_isPoissonPointFamily ((volume : Measure ℝ).prod ν)
  exact ⟨Ω, mΩ, μ, levyJumpPath hd hν b, hprob,
    isLevyProcess_levyJumpPath hd hν b,
    fun t => measurable_levyJumpPath hd hν b t,
    fun t ξ => charFun_map_levyJumpPath hd hν b t ξ⟩
