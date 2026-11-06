-- Prove2me | solution 1 for ProbabilityTheory.isCadlag_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:18:05.415196+00:00
-- url     : https://prove2.me/submissions/4469a7b1-533a-4118-972a-595890c71633

import Definitions.Def_LeanLevy_Processes_Cadlag
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Filter Set Topology ProbabilityTheory
open scoped NNReal

universe u_1 u_2

/-! Constant functions satisfy the right-continuity and left-limit clauses directly. -/
theorem solution :
    ∀ {α : Type u_1} {β : Type u_2}
      [TopologicalSpace α] [TopologicalSpace β] [Preorder α]
      {c : β}, ProbabilityTheory.IsCadlag (fun _ : α => c) := by
  intro α β _ _ _ c t
  exact ⟨continuousWithinAt_const, ⟨c, tendsto_const_nhds⟩⟩
