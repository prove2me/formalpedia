-- Prove2me | solution 1 for capScheme_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:04:08.433979+00:00
-- url     : https://prove2.me/submissions/25787543-bbdb-4328-a9dc-fce01063b073

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
variable {Z : Type*} [TopologicalSpace Z]
theorem _root_.solution (π : (ℕ → ℕ) → Z) (f : ℕ → ℕ) {m n : ℕ} (h : m ≤ n) :
    capScheme π f n ⊆ capScheme π f m :=
  closure_mono (Set.image_mono fun _ hσ i hi => hσ i (lt_of_lt_of_le hi h))
