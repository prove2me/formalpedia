-- Prove2me | solution 1 for capBelowN_update_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:15:51.640248+00:00
-- url     : https://prove2.me/submissions/a5a442d9-2253-4b71-9a4d-e52c249da984

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
theorem _root_.solution (β : ℕ → ℕ) (n k : ℕ) :
    capBelowN (Function.update β n k) (n + 1) ⊆ capBelowN β n := by
  intro σ hσ i hi
  have := hσ i (by omega)
  rwa [Function.update_of_ne (by omega)] at this
