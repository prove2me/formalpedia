-- Prove2me | solution 1 for SoficGroups.KunActualFirstStageReferenceExpansion.completedRestriction_additive_expansion_of_reference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/9c2c6a62-6b36-4945-90b8-d789d5e3a15d

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualFirstStageReferenceExpansion_completed_actual_component_additive_expansion_of_reference

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFirstStageReferenceExpansion
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunActualFirstStageReferenceExpansion
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σref σact : ι → Equiv.Perm V) (C : Finset V)
    (γ : ℝ)
    (hexpand : ∀ E : Finset V, E ⊆ C →
      2 * E.card ≤ C.card →
        γ * (E.card : ℝ) ≤ (SoficGroups.boundary σref E : ℝ)) :
    ∀ E : Finset {x : V // x ∈ C},
      γ * min (E.card : ℝ) ((C.card : ℝ) - E.card) -
        ((SoficGroups.boundary σref C : ℝ) +
          2 * (componentGeneratorDisagreement C σref σact : ℝ)) ≤
        (SoficGroups.boundary
          (fun i =>
            SoficGroups.MatchedComponentCompletion.completedRestriction
              (σact i) C) E : ℝ) := by
  apply completed_actual_component_additive_expansion_of_reference
    σref σact C
    (fun i =>
      SoficGroups.MatchedComponentCompletion.completedRestriction
        (σact i) C)
  · intro i x hx hy
    exact SoficGroups.MatchedComponentCompletion.completedRestriction_apply_of_mem
      (σact i) C x hx hy
  · exact hexpand
end SoficGroups.KunActualFirstStageReferenceExpansion
