-- Prove2me | solution 1 for SoficGroups.KunCompletedPrunedComponent.exists_completed_pruned_expander
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/26a71317-d6f0-4a43-be39-05b4867fb043

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_exists_pruned_expander
import Theorems.Thm_SoficGroups_KunCompletedPrunedComponent_boundary_expansion_of_half
import Theorems.Thm_SoficGroups_KunCompletedPrunedComponent_inducedBoundary_le_completed_boundary

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCompletedPrunedComponent
open scoped BigOperators
namespace SoficGroups.KunCompletedPrunedComponent
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (γ ell a : ℝ)
    (hgap : ell < γ)
    (hadd : ∀ A : Finset V,
      γ * min (A.card : ℝ)
          ((Fintype.card V : ℝ) - (A.card : ℝ)) -
        a * (Fintype.card V : ℝ) ≤
          (SoficGroups.boundary σ A : ℝ))
    (hsmall :
      2 * a * (2 * (γ - ell) + (Fintype.card ι : ℝ)) ≤
        (γ - ell) ^ 2) :
    ∃ (B : Finset V)
      (τ : ι → Equiv.Perm
        {x : V // x ∈ (Finset.univ \ B)}),
      2 * B.card ≤ Fintype.card V ∧
      (B.card : ℝ) ≤
        a * (Fintype.card V : ℝ) / (γ - ell) ∧
      (∀ i (x : V) (hx : x ∈ Finset.univ \ B)
        (_hy : σ i x ∈ Finset.univ \ B),
        ((τ i ⟨x, hx⟩ :
          {x : V // x ∈ Finset.univ \ B}) : V) = σ i x) ∧
      ∀ A : Finset {x : V // x ∈ Finset.univ \ B},
        ell * min (A.card : ℝ)
          ((Fintype.card {x : V // x ∈ Finset.univ \ B} : ℝ) -
            A.card) ≤ (SoficGroups.boundary τ A : ℝ) := by
  classical
  obtain ⟨B, hBhalf, hBsize, hprune⟩ :=
    SoficGroups.exists_pruned_expander σ γ ell a hgap hadd hsmall
  let Z : Finset V := Finset.univ \ B
  have hZ : Z = Finset.univ \ B := rfl
  choose τ hτ using
    (fun i : ι =>
      SoficGroups.exists_completion_of_internal_permutation
        (σ i) Z)
  have hcardZ :
      Fintype.card {x : V // x ∈ Z} =
        Fintype.card V - B.card := by
    rw [Fintype.card_coe]
    dsimp [Z]
    exact Finset.card_sdiff_of_subset (Finset.subset_univ B)
  have hexp :
      ∀ A : Finset {x : V // x ∈ Z},
        ell * min (A.card : ℝ)
          ((Fintype.card {x : V // x ∈ Z} : ℝ) - A.card) ≤
            (SoficGroups.boundary τ A : ℝ) := by
    apply boundary_expansion_of_half τ ell
    intro A hA
    let E : Finset V :=
      A.map (Function.Embedding.subtype (fun x : V => x ∈ Z))
    have hEcard : E.card = A.card := by
      dsimp [E]
      exact Finset.card_map _
    have hdisj : Disjoint B E := by
      apply Finset.disjoint_left.mpr
      intro x hxB hxE
      have hxZ : x ∈ Z :=
        Finset.property_of_mem_map_subtype A hxE
      rw [hZ] at hxZ
      exact (Finset.mem_sdiff.mp hxZ).2 hxB
    have hhalf : 2 * E.card ≤ Fintype.card V - B.card := by
      rw [hEcard, ← hcardZ]
      exact hA
    have hcut := hprune E hdisj hhalf
    have hbound :
        (SoficGroups.inducedBoundary σ B E : ℝ) ≤
          (SoficGroups.boundary τ A : ℝ) := by
      exact_mod_cast
        inducedBoundary_le_completed_boundary σ B Z hZ τ hτ A
    rw [hEcard] at hcut
    exact hcut.trans hbound
  refine ⟨B, τ, hBhalf, hBsize, ?_, ?_⟩
  · simpa only [Z] using hτ
  · intro A
    have hA := hexp A
    simpa only [Fintype.card_coe] using hA
end SoficGroups.KunCompletedPrunedComponent
