-- Prove2me | solution 1 for SoficGroups.tableGenerator_mem_tableTestSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/1f7dea30-186f-43a9-a4fc-a236ec7d1e08

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
    (F : Finset G) (h₁ : 1 ∈ F) {g : G} (hg : g ∈ F) :
    tableGenerator F h₁ ⟨g, mem_multiplicationTable_of_mem hg⟩ ∈
      tableTestSet F h₁ := by
  classical
  change _ ∈ F.attach.image _
  exact Finset.mem_image.mpr ⟨⟨g, hg⟩, Finset.mem_attach _ _, rfl⟩
end SoficGroups
