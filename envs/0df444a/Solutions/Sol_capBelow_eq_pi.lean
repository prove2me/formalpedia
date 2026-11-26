-- Prove2me | solution 1 for capBelow_eq_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:04:01.969092+00:00
-- url     : https://prove2.me/submissions/4a7cb99c-dd3d-4dc9-852c-4e64d9b821d7

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
theorem _root_.solution (β : ℕ → ℕ) :
    capBelow β = Set.pi univ (fun i => Iic (β i)) := by
  ext σ; simp [capBelow, Pi.le_def]
