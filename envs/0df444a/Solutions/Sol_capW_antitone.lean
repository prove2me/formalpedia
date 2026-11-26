-- Prove2me | solution 1 for capW_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:05:28.649921+00:00
-- url     : https://prove2.me/submissions/f8c938f2-f06a-4146-9d40-f914ca1fea89

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Finiteness
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Theorems.Thm_capTrunc_mem_capSeqs
import Theorems.Thm_capScheme_antitone
import Theorems.Thm_capScheme_trunc

set_option autoImplicit false
open Set Topology MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
variable {Z : Type*} [TopologicalSpace Z]
theorem _root_.solution (π : (ℕ → ℕ) → Z) (β : ℕ → ℕ) : Antitone (capW π β) := by
  intro m n hmn z hz
  simp only [capW, mem_iUnion] at hz ⊢
  obtain ⟨s, hs, hzs⟩ := hz
  refine ⟨capTrunc s m, ?_, ?_⟩
  · exact capTrunc_mem_capSeqs fun i hi => hs.1 i (lt_of_lt_of_le hi hmn)
  · rw [capScheme_trunc]
    exact capScheme_antitone π s hmn hzs
