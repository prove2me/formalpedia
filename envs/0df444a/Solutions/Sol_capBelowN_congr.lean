-- Prove2me | solution 1 for capBelowN_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:03:56.456124+00:00
-- url     : https://prove2.me/submissions/175faa89-ded3-472f-8029-68b4a88b8726

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
theorem _root_.solution {β β' : ℕ → ℕ} {n : ℕ} (h : ∀ i < n, β i = β' i) :
    capBelowN β n = capBelowN β' n := by
  ext σ; constructor <;> intro hσ i hi
  · rw [← h i hi]; exact hσ i hi
  · rw [h i hi]; exact hσ i hi
