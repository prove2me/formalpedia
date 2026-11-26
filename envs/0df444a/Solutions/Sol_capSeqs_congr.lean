-- Prove2me | solution 1 for capSeqs_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:04:07.691348+00:00
-- url     : https://prove2.me/submissions/5069e44a-8412-41ba-bd8a-10749ce8284c

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
    capSeqs β n = capSeqs β' n := by
  ext s
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨fun i hi => ?_, h2⟩
  · rw [← h i hi]; exact h1 i hi
  · rw [h i hi]; exact h1 i hi
