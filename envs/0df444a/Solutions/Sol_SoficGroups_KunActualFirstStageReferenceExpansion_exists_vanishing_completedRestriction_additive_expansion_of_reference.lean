-- Prove2me | solution 1 for SoficGroups.KunActualFirstStageReferenceExpansion.exists_vanishing_completedRestriction_additive_expansion_of_reference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/36e0bd0c-902a-4d7a-af60-4446181284c4

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualFirstStageReferenceExpansion_completedRestriction_additive_expansion_of_reference
import Theorems.Thm_SoficGroups_KunActualFirstStageReferenceExpansion_normalizedReferenceCompletionError_tendsto_zero

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
    (C : (n : ℕ) → Finset (V n))
    (hC : ∀ n, (C n).Nonempty)
    (σref σact : (n : ℕ) → ι → Equiv.Perm (V n))
    (γ : ℝ)
    (hexpand : ∀ n, ∀ E : Finset (V n), E ⊆ C n →
      2 * E.card ≤ (C n).card →
        γ * (E.card : ℝ) ≤
          (SoficGroups.boundary (σref n) E : ℝ))
    (hboundary : Tendsto
      (fun n =>
        (SoficGroups.boundary (σref n) (C n) : ℝ) /
          (C n).card)
      atTop (nhds 0))
    (hdisagreement : Tendsto
      (fun n =>
        (componentGeneratorDisagreement
          (C n) (σref n) (σact n) : ℝ) / (C n).card)
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
  let a : ℕ → ℝ :=
    fun n => normalizedReferenceCompletionError
      (C n) (σref n) (σact n)
  refine ⟨a, ?_, ?_, ?_⟩
  · intro n
    unfold a normalizedReferenceCompletionError
    apply div_nonneg
    · positivity
    · exact Nat.cast_nonneg _
  · exact normalizedReferenceCompletionError_tendsto_zero
      V ι C σref σact hboundary hdisagreement
  · intro n E
    have hcard : ((C n).card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr (hC n)
    have h :=
      completedRestriction_additive_expansion_of_reference
        (σref n) (σact n) (C n) γ (hexpand n) E
    simpa only [a, normalizedReferenceCompletionError,
      Fintype.card_coe, div_mul_cancel₀ _ hcard] using h
end SoficGroups.KunActualFirstStageReferenceExpansion
