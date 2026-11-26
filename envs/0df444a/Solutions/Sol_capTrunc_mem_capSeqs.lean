-- Prove2me | solution 1 for capTrunc_mem_capSeqs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:01:47.284907+00:00
-- url     : https://prove2.me/submissions/5ba751e9-ac16-46d3-81f2-f0b2b57b25fb

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Finiteness
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability

set_option autoImplicit false
open Set Topology MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
theorem _root_.solution {β : ℕ → ℕ} {n : ℕ} {σ : ℕ → ℕ}
    (h : σ ∈ capBelowN β n) : capTrunc σ n ∈ capSeqs β n := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · simp only [capTrunc, if_pos hi]; exact h i hi
  · have hn : ¬ i < n := by omega
    simp [capTrunc, hn]
