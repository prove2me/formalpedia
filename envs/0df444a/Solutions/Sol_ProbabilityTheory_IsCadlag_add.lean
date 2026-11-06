-- Prove2me | solution 1 for ProbabilityTheory.IsCadlag.add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:38:26.69397+00:00
-- url     : https://prove2.me/submissions/3bb16bee-ce59-46d5-baf5-1ad35f394122

import Definitions.Def_LeanLevy_Processes_Cadlag
import Mathlib.Topology.Algebra.Monoid.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Filter Set Topology ProbabilityTheory
variable {α : Type*} [TopologicalSpace α] [Preorder α]

theorem solution {β : Type*} [TopologicalSpace β] [AddCommMonoid β] [ContinuousAdd β]
    {f g : α → β} (hf : IsCadlag f) (hg : IsCadlag g) :
    IsCadlag (fun s => f s + g s) := by
  intro t
  obtain ⟨hfc, lf, hlf⟩ := hf t
  obtain ⟨hgc, lg, hlg⟩ := hg t
  exact ⟨hfc.add hgc, lf + lg, hlf.add hlg⟩
