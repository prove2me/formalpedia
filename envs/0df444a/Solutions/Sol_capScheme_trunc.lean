-- Prove2me | solution 1 for capScheme_trunc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:04:47.994773+00:00
-- url     : https://prove2.me/submissions/e76db08b-7344-4759-b7ff-881358d88544

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Finiteness
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Theorems.Thm_capScheme_congr

set_option autoImplicit false
open Set Topology MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
variable {Z : Type*} [TopologicalSpace Z]
theorem _root_.solution (π : (ℕ → ℕ) → Z) (σ : ℕ → ℕ) (n : ℕ) :
    capScheme π (capTrunc σ n) n = capScheme π σ n :=
  capScheme_congr π fun i hi => by simp [capTrunc, if_pos hi]
