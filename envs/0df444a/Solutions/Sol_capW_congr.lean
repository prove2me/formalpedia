-- Prove2me | solution 1 for capW_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:04:44.852686+00:00
-- url     : https://prove2.me/submissions/ab37ea26-0ba0-4a8e-922f-5cb1af396fd8

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Finiteness
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Theorems.Thm_capSeqs_congr

set_option autoImplicit false
open Set Topology MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
variable {Z : Type*} [TopologicalSpace Z]
theorem _root_.solution (π : (ℕ → ℕ) → Z) {β β' : ℕ → ℕ} {n : ℕ}
    (h : ∀ i < n, β i = β' i) : capW π β n = capW π β' n := by
  unfold capW
  rw [capSeqs_congr h]
