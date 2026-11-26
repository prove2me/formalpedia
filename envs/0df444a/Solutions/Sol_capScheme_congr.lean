-- Prove2me | solution 1 for capScheme_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:04:11.612895+00:00
-- url     : https://prove2.me/submissions/2a2e1a09-b985-4a0f-bceb-fbf1449ecaef

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
theorem _root_.solution (π : (ℕ → ℕ) → Z) {f g : ℕ → ℕ} {n : ℕ}
    (h : ∀ i < n, f i = g i) : capScheme π f n = capScheme π g n := by
  have hcyl : PiNat.cylinder f n = PiNat.cylinder g n := by
    ext σ
    simp only [PiNat.mem_cylinder_iff]
    constructor <;> intro hσ i hi
    · rw [← h i hi]; exact hσ i hi
    · rw [h i hi]; exact hσ i hi
  unfold capScheme
  rw [hcyl]
