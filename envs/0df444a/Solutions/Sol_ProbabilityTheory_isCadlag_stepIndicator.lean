-- Prove2me | solution 1 for ProbabilityTheory.isCadlag_stepIndicator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:35:32.544478+00:00
-- url     : https://prove2.me/submissions/bc531b49-4396-41ec-b850-47ee1066abf6

import Definitions.Def_LeanLevy_Processes_Cadlag
import Mathlib.Topology.Order.OrderClosed
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology ProbabilityTheory
open scoped NNReal

theorem solution {c y : ℝ} :
    IsCadlag (fun t : ℝ => if c ≤ t then y else 0) := by
  intro t
  constructor
  · rcases lt_or_ge t c with ht | ht
    · have heq : (fun s : ℝ => if c ≤ s then y else 0) =ᶠ[𝓝[Ici t] t] fun _ => (0 : ℝ) := by
        filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ht)] with s hs
        simp only [if_neg (not_le.mpr (Set.mem_Iio.mp hs))]
      refine continuousWithinAt_const.congr_of_eventuallyEq heq ?_
      simp only [if_neg (not_le.mpr ht)]
    · have heq : (fun s : ℝ => if c ≤ s then y else 0) =ᶠ[𝓝[Ici t] t] fun _ => y := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [if_pos (le_trans ht hs)]
      refine continuousWithinAt_const.congr_of_eventuallyEq heq ?_
      simp only [if_pos ht]
  · rcases le_or_gt t c with ht | ht
    · refine ⟨0, ?_⟩
      have heq : (fun s : ℝ => if c ≤ s then y else 0) =ᶠ[𝓝[Iio t] t] fun _ => (0 : ℝ) := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [if_neg (not_le.mpr (lt_of_lt_of_le hs ht))]
      exact tendsto_const_nhds.congr' heq.symm
    · refine ⟨y, ?_⟩
      have heq : (fun s : ℝ => if c ≤ s then y else 0) =ᶠ[𝓝[Iio t] t] fun _ => y := by
        filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds ht)] with s hs
        simp only [if_pos (le_of_lt (Set.mem_Ioi.mp hs))]
      exact tendsto_const_nhds.congr' heq.symm
