-- Prove2me | solution 1 for capR_subset_capW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:05:39.059988+00:00
-- url     : https://prove2.me/submissions/9de2c8ce-e745-4f19-b1dd-6d352df774ea

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Finiteness
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Theorems.Thm_capTrunc_mem_capSeqs
import Theorems.Thm_capScheme_trunc

set_option autoImplicit false
open Set Topology MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
variable {Z : Type*} [TopologicalSpace Z]
theorem _root_.solution (π : (ℕ → ℕ) → Z) (β : ℕ → ℕ) (n : ℕ) :
    capR π β n ⊆ capW π β n := by
  intro z hz
  simp only [capR, mem_iUnion, exists_prop] at hz
  obtain ⟨σ, hσ, hz⟩ := hz
  have h1 : z ∈ capScheme π σ n := mem_iInter.mp hz n
  exact mem_biUnion (capTrunc_mem_capSeqs hσ) (by rwa [capScheme_trunc])
