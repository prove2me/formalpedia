-- Prove2me | solution 1 for SoficGroups.exists_finite_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/ba08a5fd-0090-47c6-a84a-6c0418e5560c

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {G : Type*} [Group G] (hG : ¬ Sofic G) :
    ∃ (F : Finset G) (ε : ℝ), 1 ∈ F ∧ 0 < ε ∧ ε < 1 ∧
      ∀ M : PermutationModel G, ¬ GoodOn M F ε := by
  classical
  have hex : ∃ (F : Finset G) (ε : ℝ), 0 < ε ∧ ε < 1 ∧
      ∀ M : PermutationModel G, ¬ GoodOn M F ε := by
    by_contra h
    apply hG
    constructor
    intro F ε hε hε'
    by_contra hmodel
    apply h
    exact ⟨F, ε, hε, hε', fun M hM => hmodel ⟨M, hM⟩⟩
  obtain ⟨F, ε, hε, hε', hF⟩ := hex
  refine ⟨insert 1 F, ε, Finset.mem_insert_self _ _, hε, hε', ?_⟩
  intro M hM
  exact hF M (hM.mono (Finset.subset_insert _ _))
end SoficGroups
