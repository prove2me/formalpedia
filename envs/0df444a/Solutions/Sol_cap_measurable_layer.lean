-- Prove2me | solution 1 for cap_measurable_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:05:43.865528+00:00
-- url     : https://prove2.me/submissions/e4f5f437-5062-4071-b4dc-96239db36b09

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Finiteness
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Theorems.Thm_isClosed_capW
import Theorems.Thm_capW_congr

set_option autoImplicit false
open Set Topology MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
variable {Z : Type*} [TopologicalSpace Z]
open ProbabilityTheory
variable {X Y : Type*}
  [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
omit [PolishSpace X]
theorem _root_.solution
    (π : (ℕ → ℕ) → (X × Y)) (κ : Kernel X Y) [IsSFiniteKernel κ]
    (q : ℝ≥0∞) (n : ℕ) :
    MeasurableSet {p : X × (ℕ → ℕ) |
      q < κ p.1 (Prod.mk p.1 ⁻¹' capW π p.2 n)} := by
  have hdecomp : {p : X × (ℕ → ℕ) | q < κ p.1 (Prod.mk p.1 ⁻¹' capW π p.2 n)}
      = ⋃ b : Fin n → ℕ,
          ({x | q < κ x (Prod.mk x ⁻¹' capW π (capPad n b) n)} ×ˢ
           {β : ℕ → ℕ | ∀ i : Fin n, β i = b i}) := by
    ext ⟨x, β⟩
    simp only [mem_ofPred_eq, mem_iUnion, mem_prod]
    constructor
    · intro hq
      refine ⟨fun i => β i, ?_, fun i => rfl⟩
      have hW : capW π (capPad n (fun i : Fin n => β i)) n = capW π β n :=
        capW_congr π fun i hi => by simp [capPad, hi]
      rw [hW]; exact hq
    · rintro ⟨b, hq, hb⟩
      have hW : capW π β n = capW π (capPad n b) n :=
        capW_congr π fun i hi => by
          have := hb ⟨i, hi⟩
          simp [capPad, hi, this]
      rw [hW]; exact hq
  rw [hdecomp]
  refine MeasurableSet.iUnion fun b => MeasurableSet.prod ?_ ?_
  · exact measurableSet_lt measurable_const
      (Kernel.measurable_kernel_prodMk_left (isClosed_capW π _ n).measurableSet)
  · have : {β : ℕ → ℕ | ∀ i : Fin n, β i = b i}
        = ⋂ i : Fin n, (fun β : ℕ → ℕ => β i) ⁻¹' {b i} := by
      ext β; simp
    rw [this]
    exact MeasurableSet.iInter fun i =>
      (measurable_pi_apply (i : ℕ)) (measurableSet_singleton (b i))
