-- Prove2me | solution 1 for capKernel_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:06:05.908637+00:00
-- url     : https://prove2.me/submissions/e7fbbc27-05be-4421-abde-7832adb430a7

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Finiteness
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Theorems.Thm_capTrunc_mem_capSeqs
import Theorems.Thm_capScheme_trunc
import Theorems.Thm_iInter_capW_subset
import Theorems.Thm_range_subset_capKernel

set_option autoImplicit false
open Set Topology MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
variable {Z : Type*} [TopologicalSpace Z]
theorem _root_.solution {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    {π : (ℕ → ℕ) → Z} (hπ : Continuous π) : capKernel π = range π := by
  refine subset_antisymm ?_ (range_subset_capKernel π)
  intro z hz
  obtain ⟨σ, hσ⟩ := mem_iUnion.mp hz
  have h1 : z ∈ ⋂ n, capW π σ n := by
    refine mem_iInter.mpr fun n => ?_
    have h2 := mem_iInter.mp hσ n
    exact mem_biUnion (capTrunc_mem_capSeqs fun i _ => le_refl (σ i))
      (by rwa [capScheme_trunc])
  obtain ⟨ρ, _, rfl⟩ := iInter_capW_subset hπ σ h1
  exact mem_range_self ρ
