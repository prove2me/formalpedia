-- Prove2me | solution 1 for SoficGroups.exists_nonsofic_finite_table
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/2811580b-49e6-4152-9c75-7d97f98917b0

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_exists_finite_obstruction
import Theorems.Thm_SoficGroups_tableGroup_finitelyPresented
import Theorems.Thm_SoficGroups_tableGroup_not_sofic_of_obstruction

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {G : Type u} [Group G]
    (hG : ¬ Sofic G) :
    ∃ (F : Finset G) (h₁ : 1 ∈ F),
      Group.IsFinitelyPresented (tableGroup F h₁) ∧
        ¬ Sofic (tableGroup F h₁) := by
  obtain ⟨F, ε, h₁, hε, hε', hbad⟩ := exists_finite_obstruction hG
  exact ⟨F, h₁, tableGroup_finitelyPresented F h₁,
    tableGroup_not_sofic_of_obstruction F h₁ ε hε hε' hbad⟩
end SoficGroups
