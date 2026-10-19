-- Prove2me | solution 1 for SoficGroups.KunActualFirstStageReferenceExpansion.exists_vanishing_completedRestriction_additive_expansion_of_selected_bad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/67df844f-6b3a-4e1e-b665-ea713a9b8aab

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualFirstStageReferenceExpansion_exists_vanishing_completedRestriction_additive_expansion_of_reference
import Theorems.Thm_SoficGroups_KunActualFirstStageReferenceExpansion_componentGeneratorDisagreement_density_tendsto_zero_of_component_bad

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFirstStageReferenceExpansion
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunActualFirstStageReferenceExpansion
theorem _root_.solution
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (ι : Type*) [Fintype ι]
    (C B : (n : ℕ) → Finset (V n))
    (hC : ∀ n, (C n).Nonempty)
    (σref σact : (n : ℕ) → ι → Equiv.Perm (V n))
    (γ : ℝ)
    (hexpand : ∀ n, ∀ E : Finset (V n), E ⊆ C n →
      2 * E.card ≤ (C n).card →
        γ * (E.card : ℝ) ≤
          (SoficGroups.boundary (σref n) E : ℝ))
    (hbad : ∀ n i (x : V n), x ∈ C n →
      σref n i x ≠ σact n i x → x ∈ B n)
    (hboundary : Tendsto
      (fun n =>
        (SoficGroups.boundary (σref n) (C n) : ℝ) /
          (C n).card)
      atTop (nhds 0))
    (hbad_density : Tendsto
      (fun n =>
        (((C n ∩ B n).card : ℝ) / (C n).card))
      atTop (nhds 0)) :
    ∃ a : ℕ → ℝ,
      (∀ n, 0 ≤ a n) ∧
      Tendsto a atTop (nhds 0) ∧
      ∀ n, ∀ E : Finset {x : V n // x ∈ C n},
        γ * min (E.card : ℝ)
          ((Fintype.card {x : V n // x ∈ C n} : ℝ) - E.card) -
            a n * Fintype.card {x : V n // x ∈ C n} ≤
          (SoficGroups.boundary
            (fun i =>
              SoficGroups.MatchedComponentCompletion.completedRestriction
                (σact n i) (C n)) E : ℝ) := by
  apply exists_vanishing_completedRestriction_additive_expansion_of_reference
    V ι C hC σref σact γ hexpand hboundary
  exact componentGeneratorDisagreement_density_tendsto_zero_of_component_bad
    V ι C B σref σact hbad hbad_density
end SoficGroups.KunActualFirstStageReferenceExpansion
