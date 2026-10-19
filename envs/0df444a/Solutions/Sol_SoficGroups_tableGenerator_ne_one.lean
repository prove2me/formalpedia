-- Prove2me | solution 1 for SoficGroups.tableGenerator_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/1921fed0-704d-42f3-8175-e84613e896cd

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) {g : G} (hg : g ∈ F) (hne : g ≠ 1) :
    tableGenerator F h₁ ⟨g, mem_multiplicationTable_of_mem hg⟩ ≠ 1 := by
  intro h
  apply hne
  simpa using congrArg (tableEvaluation F h₁) h
end SoficGroups
