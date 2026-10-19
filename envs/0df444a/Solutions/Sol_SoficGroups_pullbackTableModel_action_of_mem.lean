-- Prove2me | solution 1 for SoficGroups.pullbackTableModel_action_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/e6ce5452-bec5-41a3-8b50-4e9e90920456

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
    (F : Finset G) (h₁ : 1 ∈ F)
    (M : PermutationModel (tableGroup F h₁))
    {g : G} (hg : g ∈ multiplicationTable F) :
    (pullbackTableModel F h₁ M).action g =
      M.action (tableGenerator F h₁ ⟨g, hg⟩) := by
  classical
  simp only [pullbackTableModel, dif_pos hg]
end SoficGroups
