-- Prove2me | solution 1 for SoficGroups.KunCompletedPrunedComponent.boundary_expansion_of_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/e2379531-8a77-4831-bdbf-43921214fe34

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_boundary_complement
import Theorems.Thm_SoficGroups_KunCompletedPrunedComponent_boundary_complement

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCompletedPrunedComponent
open scoped BigOperators
namespace SoficGroups.KunCompletedPrunedComponent
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (h : ℝ)
    (hhalf : ∀ A : Finset V,
      2 * A.card ≤ Fintype.card V →
        h * (A.card : ℝ) ≤ (SoficGroups.boundary σ A : ℝ)) :
    ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (SoficGroups.boundary σ A : ℝ) := by
  classical
  intro A
  by_cases hA : 2 * A.card ≤ Fintype.card V
  · have hAreal :
        (2 : ℝ) * A.card ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hA
    rw [min_eq_left (by linarith)]
    exact hhalf A hA
  · let C : Finset V := Finset.univ \ A
    have hcard : C.card + A.card = Fintype.card V := by
      dsimp [C]
      simpa using
        (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A))
    have hChalf : 2 * C.card ≤ Fintype.card V := by
      omega
    have hC := hhalf C hChalf
    have hAreal :
        (Fintype.card V : ℝ) < (2 : ℝ) * A.card := by
      exact_mod_cast Nat.lt_of_not_ge hA
    have hCreal :
        (C.card : ℝ) = (Fintype.card V : ℝ) - A.card := by
      have hcardReal :
          (C.card : ℝ) + A.card = (Fintype.card V : ℝ) := by
        exact_mod_cast hcard
      linarith
    rw [min_eq_right (by linarith)]
    rw [hCreal] at hC
    simpa [C, boundary_complement] using hC
end SoficGroups.KunCompletedPrunedComponent
