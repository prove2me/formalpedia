-- Prove2me | solution 1 for SoficGroups.KunResidualExpanderDecomposition.completeCleanFinpartition_half_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/d2ebeafa-fa6f-4a0e-a659-6ce6b80c39c0

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualExpanderDecomposition
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.KunResidualExpanderDecomposition
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B : Finset V)
    (P : Finpartition (Finset.univ \ B)) (γ : ℝ)
    (hexpand : ∀ C ∈ P.parts, ∀ E : Finset V, E ⊆ C →
      2 * E.card ≤ C.card →
        γ * (E.card : ℝ) ≤ (SoficGroups.boundary σ E : ℝ)) :
    ∀ C ∈ (completeCleanFinpartition B P).parts,
      ∀ E : Finset V, E ⊆ C →
        2 * E.card ≤ C.card →
          γ * (E.card : ℝ) ≤ (SoficGroups.boundary σ E : ℝ) := by
  classical
  intro C hC E hEC hhalf
  rw [completeCleanFinpartition_parts] at hC
  rcases Finset.mem_union.mp hC with hclean | hbad
  · exact hexpand C hclean E hEC hhalf
  · obtain ⟨x, _, hx⟩ := Finpartition.mem_bot_iff.mp hbad
    subst C
    have hE : E = ∅ := by
      apply Finset.card_eq_zero.mp
      simp only [Finset.card_singleton] at hhalf
      omega
    subst E
    simp [SoficGroups.boundary]
end SoficGroups.KunResidualExpanderDecomposition
