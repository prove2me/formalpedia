-- Prove2me | solution 1 for ProbabilityTheory.IsLevyProcess.charFun_marginal_cpow
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T13:18:09.508308+00:00
-- url     : https://prove2.me/submissions/ce4218fe-cd9b-47f1-ba73-28dd0ba226ae

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Defs.Basic
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_levyLocalCharExponent_eq_charExponent
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_charFun_eq_exp_mul
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_charFun_marginal_ne_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Topology ProbabilityTheory Complex
open scoped NNReal

universe u v

/-- Source original marginal complex-power identity. -/
theorem solution
    {Ω : Sort (u + 1)} [MeasurableSpace Ω]
    {E : Sort (v + 1)} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E] {X : ℝ≥0 → Ω → E} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) :
    ∃ ε > 0, ∀ ξ ∈ Metric.ball (0 : E) ε, ∀ t : ℝ≥0,
      charFun (μ.map (X t)) ξ = (charFun (μ.map (X 1)) ξ) ^ (↑(t : ℝ) : ℂ) := by
  obtain ⟨ε, hε, hball⟩ := h.levyLocalCharExponent_eq_charExponent hX
  refine ⟨ε, hε, fun ξ hξ t => ?_⟩
  have hne : charFun (μ.map (X 1)) ξ ≠ 0 := h.charFun_marginal_ne_zero hX 1 ξ
  rw [Complex.cpow_def_of_ne_zero hne, h.charFun_eq_exp_mul hX t ξ]
  congr 1
  have hψ_eq := hball ξ hξ
  simp only [IsLevyProcess.levyLocalCharExponent, LocalLog.localCharExponent] at hψ_eq
  rw [← hψ_eq]
  ring
