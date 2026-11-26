-- Prove2me | solution 1 for capR_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:04:33.321576+00:00
-- url     : https://prove2.me/submissions/ee89ed9c-1474-4fe2-962b-5a7a94e1b03c

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Finiteness
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Theorems.Thm_capBelowN_congr

set_option autoImplicit false
open Set Topology MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
variable {Z : Type*} [TopologicalSpace Z]
theorem _root_.solution (π : (ℕ → ℕ) → Z) {β β' : ℕ → ℕ} {n : ℕ}
    (h : ∀ i < n, β i = β' i) : capR π β n = capR π β' n := by
  unfold capR
  rw [capBelowN_congr h]
