-- Prove2me | solution 1 for StochKnapSL.CapacityGap.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:38:09.325696+00:00
-- url     : https://prove2.me/submissions/d3e232c4-9f40-4389-8e11-d248194fde1e

import Mathlib
import Definitions.Def_StochKnapSL_CapacityGap_Model
import Theorems.Thm_StochKnapSL_CapacityGap_theorem_3
import Theorems.Thm_StochKnapSL_CapacityGap_theorem_4
open MeasureTheory ProbabilityTheory
open StochKnapSL.CapacityGap

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (d : Fin N → Ω → ℝ) (Δ : ℝ) (α : Fin N → ℝ)
    (hS : Standing μ d Δ α) :
    QAnti μ d α - QAdap μ d α ≤ 2 * Δ := by
  have h3 := theorem_3 μ d Δ α hS
  have h4 := theorem_4 μ d Δ α hS
  linarith
