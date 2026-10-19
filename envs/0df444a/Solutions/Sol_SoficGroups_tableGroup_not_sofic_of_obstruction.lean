-- Prove2me | solution 1 for SoficGroups.tableGroup_not_sofic_of_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/1ccef4dd-2e45-41a9-b893-b552332072eb

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_goodOn_pullbackTableModel

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) (ε : ℝ)
    (hε : 0 < ε) (hε' : ε < 1)
    (hbad : ∀ M : PermutationModel G, ¬ GoodOn M F ε) :
    ¬ Sofic (tableGroup F h₁) := by
  intro hsofic
  obtain ⟨M, hM⟩ := hsofic.approximation (tableTestSet F h₁) ε hε hε'
  exact hbad (pullbackTableModel F h₁ M)
    (goodOn_pullbackTableModel F h₁ M hM)
end SoficGroups
