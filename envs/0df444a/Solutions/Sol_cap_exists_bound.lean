-- Prove2me | solution 1 for cap_exists_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:06:38.929488+00:00
-- url     : https://prove2.me/submissions/b341c484-7bfb-407e-b704-bf15cb061f39

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Finiteness
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Theorems.Thm_capR_congr
import Theorems.Thm_capR_subset_capW
import Theorems.Thm_capAux_eq

set_option autoImplicit false
open Set Topology MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
variable {Z : Type*} [TopologicalSpace Z]
theorem _root_.solution {Z : Type*} [TopologicalSpace Z]
    (π : (ℕ → ℕ) → Z) (m : Set Z → ℝ≥0∞)
    (hmono : ∀ ⦃S T : Set Z⦄, S ⊆ T → m S ≤ m T)
    (hsup : ∀ s : ℕ → Set Z, Monotone s → m (⋃ k, s k) = ⨆ k, m (s k))
    {c : ℝ≥0∞} (h0 : c < m (capKernel π)) :
    ∃ β : ℕ → ℕ, ∀ n, c < m (capW π β n) := by
  refine ⟨capBound π m hsup h0, fun n => ?_⟩
  have h1 : c < m (capR π (capAux π m hsup h0 n).val n) := (capAux π m hsup h0 n).2
  have h2 : capR π (capAux π m hsup h0 n).val n
      = capR π (capBound π m hsup h0) n :=
    capR_congr π fun i hi => capAux_eq π m hsup h0 n i hi
  rw [h2] at h1
  exact lt_of_lt_of_le h1 (hmono (capR_subset_capW π _ n))
