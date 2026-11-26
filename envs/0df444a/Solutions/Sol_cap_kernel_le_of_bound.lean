-- Prove2me | solution 1 for cap_kernel_le_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:09:11.10791+00:00
-- url     : https://prove2.me/submissions/f01c2617-2a8c-4118-80c1-ea38f224c7f5

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Finiteness
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Theorems.Thm_isClosed_capW
import Theorems.Thm_capW_antitone
import Theorems.Thm_iInter_capW_subset
import Theorems.Thm_MeasureTheory_AnalyticSet_nullMeasurableSet

set_option autoImplicit false
open Set Topology MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
variable {Z : Type*} [TopologicalSpace Z]
open ProbabilityTheory
variable {X Y : Type*}
  [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
omit [BorelSpace X]
theorem _root_.solution
    {π : (ℕ → ℕ) → (X × Y)} (hπ : Continuous π)
    (κ : Kernel X Y) [IsFiniteKernel κ] {x : X} {c : ℝ≥0∞} {β : ℕ → ℕ}
    (h : ∀ n, c < κ x (Prod.mk x ⁻¹' capW π β n)) :
    c ≤ κ x (Prod.mk x ⁻¹' range π) := by
  have hmeas : ∀ n, NullMeasurableSet (Prod.mk x ⁻¹' capW π β n) (κ x) := fun n =>
    (((isClosed_capW π β n).preimage
      (Continuous.prodMk continuous_const continuous_id)).measurableSet).nullMeasurableSet
  have h_iInter : κ x (⋂ n, Prod.mk x ⁻¹' capW π β n)
      = ⨅ n, κ x (Prod.mk x ⁻¹' capW π β n) :=
    Directed.measure_iInter hmeas
      (fun i j => ⟨max i j,
        preimage_mono (capW_antitone π β (le_max_left i j)),
        preimage_mono (capW_antitone π β (le_max_right i j))⟩)
      ⟨0, measure_ne_top _ _⟩
  calc c ≤ ⨅ n, κ x (Prod.mk x ⁻¹' capW π β n) := le_iInf fun n => (h n).le
    _ = κ x (⋂ n, Prod.mk x ⁻¹' capW π β n) := h_iInter.symm
    _ ≤ κ x (Prod.mk x ⁻¹' (π '' capBelow β)) := by
        refine measure_mono ?_
        rw [← preimage_iInter]
        exact preimage_mono (iInter_capW_subset hπ β)
    _ ≤ κ x (Prod.mk x ⁻¹' range π) :=
        measure_mono (preimage_mono (image_subset_range π _))
