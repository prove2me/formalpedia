-- Prove2me | solution 1 for ProbabilityTheory.IsCadlagAt.congr
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:39:20.820126+00:00
-- url     : https://prove2.me/submissions/9fbe7c76-ee46-4f5d-a053-5d7a38466d0c

import Definitions.Def_LeanLevy_Processes_Cadlag
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Topology.Defs.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Filter Set Topology ProbabilityTheory
variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Preorder α]

theorem solution {f g : α → β} {t : α} (hf : IsCadlagAt f t)
    (h : f =ᶠ[𝓝 t] g) : IsCadlagAt g t := by
  obtain ⟨hc, l, hl⟩ := hf
  refine ⟨?_, l, ?_⟩
  · exact hc.congr_of_eventuallyEq (h.filter_mono nhdsWithin_le_nhds).symm h.eq_of_nhds.symm
  · exact hl.congr' (h.filter_mono nhdsWithin_le_nhds)
