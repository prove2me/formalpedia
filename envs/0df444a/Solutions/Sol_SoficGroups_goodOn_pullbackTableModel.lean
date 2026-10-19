-- Prove2me | solution 1 for SoficGroups.goodOn_pullbackTableModel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/7a03963e-fdcc-465d-a445-5ff038aae6aa

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_tableGenerator_mul
import Theorems.Thm_SoficGroups_tableGenerator_ne_one
import Theorems.Thm_SoficGroups_tableGenerator_mem_tableTestSet
import Theorems.Thm_SoficGroups_pullbackTableModel_action_of_mem

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) {ε : ℝ}
    (M : PermutationModel (tableGroup F h₁))
    (hM : GoodOn M (tableTestSet F h₁) ε) :
    GoodOn (pullbackTableModel F h₁ M) F ε := by
  constructor
  · intro g hg h hh
    have htest := hM.multiplicative
      (tableGenerator F h₁ ⟨g, mem_multiplicationTable_of_mem hg⟩)
      (tableGenerator_mem_tableTestSet F h₁ hg)
      (tableGenerator F h₁ ⟨h, mem_multiplicationTable_of_mem hh⟩)
      (tableGenerator_mem_tableTestSet F h₁ hh)
    change normalizedHamming
      ((pullbackTableModel F h₁ M).action (g * h))
      ((pullbackTableModel F h₁ M).action g *
        (pullbackTableModel F h₁ M).action h) < ε
    rw [pullbackTableModel_action_of_mem F h₁ M
      (mul_mem_multiplicationTable hg hh),
      pullbackTableModel_action_of_mem F h₁ M
        (mem_multiplicationTable_of_mem hg),
      pullbackTableModel_action_of_mem F h₁ M
        (mem_multiplicationTable_of_mem hh),
      ← tableGenerator_mul F h₁ hg hh]
    exact htest
  · intro g hg hne
    have htest := hM.separated
      (tableGenerator F h₁ ⟨g, mem_multiplicationTable_of_mem hg⟩)
      (tableGenerator_mem_tableTestSet F h₁ hg)
      (tableGenerator_ne_one F h₁ hg hne)
    change 1 - ε < normalizedHamming
      ((pullbackTableModel F h₁ M).action g) 1
    rw [pullbackTableModel_action_of_mem F h₁ M
      (mem_multiplicationTable_of_mem hg)]
    exact htest
end SoficGroups
