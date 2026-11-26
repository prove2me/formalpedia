-- Prove2me | solution 1 for cap_kernel_exists_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:07:27.567142+00:00
-- url     : https://prove2.me/submissions/3db3aae9-1796-4ceb-86c3-baea4061fc16

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Finiteness
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Theorems.Thm_capKernel_eq_range
import Theorems.Thm_cap_exists_bound

set_option autoImplicit false
open Set Topology MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
variable {Z : Type*} [TopologicalSpace Z]
open ProbabilityTheory
variable {X Y : Type*}
  [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
omit [BorelSpace X] [BorelSpace Y]
theorem _root_.solution
    {π : (ℕ → ℕ) → (X × Y)} (hπ : Continuous π)
    (κ : Kernel X Y) {x : X} {c : ℝ≥0∞}
    (hc : c < κ x (Prod.mk x ⁻¹' range π)) :
    ∃ β : ℕ → ℕ, ∀ n, c < κ x (Prod.mk x ⁻¹' capW π β n) := by
  have h0 : c < κ x (Prod.mk x ⁻¹' capKernel π) := by
    rwa [capKernel_eq_range hπ]
  exact cap_exists_bound π (fun S => κ x (Prod.mk x ⁻¹' S))
    (fun _ _ hST => measure_mono (preimage_mono hST))
    (fun s hs => by
      show (κ x) (Prod.mk x ⁻¹' ⋃ k, s k) = ⨆ k, (κ x) (Prod.mk x ⁻¹' s k)
      rw [preimage_iUnion]
      exact Monotone.measure_iUnion fun i j hij => preimage_mono (hs hij))
    h0
