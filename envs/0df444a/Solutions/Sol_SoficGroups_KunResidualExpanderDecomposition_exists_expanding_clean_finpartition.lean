-- Prove2me | solution 1 for SoficGroups.KunResidualExpanderDecomposition.exists_expanding_clean_finpartition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/61c71c9c-5e70-4dbb-acfd-1af69bc5a92c

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_boundary_complement
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_boundary_le_degree_mul_card
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_exists_expanding_residual_finpartition

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualExpanderDecomposition
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.KunResidualExpanderDecomposition
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B : Finset V) (γ α : ℝ)
    (hα : 0 ≤ α)
    (himprove : ∀ T : Finset V, T ⊆ Finset.univ \ B →
      (SoficGroups.boundary σ T : ℝ) < γ * (T.card : ℝ) →
      ∃ U : Finset V, 3 * (U ∆ T).card < T.card ∧
        (SoficGroups.boundary σ U : ℝ) ≤ α * (U.card : ℝ)) :
    ∃ P : Finpartition (Finset.univ \ B),
      (∀ C ∈ P.parts, ∀ E : Finset V, E ⊆ C →
        2 * E.card ≤ C.card →
          γ * (E.card : ℝ) ≤ (SoficGroups.boundary σ E : ℝ)) ∧
      (∑ C ∈ P.parts, (SoficGroups.boundary σ C : ℝ)) ≤
        (Fintype.card ι : ℝ) * (B.card : ℝ) +
          4 * α * ((Finset.univ \ B).card : ℝ) := by
  obtain ⟨P, hP, hbudget⟩ :=
    exists_expanding_residual_finpartition σ B γ α hα himprove
      (Finset.univ \ B) (Finset.Subset.refl _)
  refine ⟨P, hP, ?_⟩
  calc
    (∑ C ∈ P.parts, (SoficGroups.boundary σ C : ℝ)) ≤
        (SoficGroups.boundary σ (Finset.univ \ B) : ℝ) +
          4 * α * ((Finset.univ \ B).card : ℝ) := hbudget
    _ = (SoficGroups.boundary σ B : ℝ) +
          4 * α * ((Finset.univ \ B).card : ℝ) := by
            rw [boundary_complement]
    _ ≤ (Fintype.card ι : ℝ) * (B.card : ℝ) +
          4 * α * ((Finset.univ \ B).card : ℝ) := by
            have hdegree := boundary_le_degree_mul_card σ B
            have hdegreeReal :
                (SoficGroups.boundary σ B : ℝ) ≤
                  (Fintype.card ι : ℝ) * (B.card : ℝ) := by
              exact_mod_cast hdegree
            linarith
end SoficGroups.KunResidualExpanderDecomposition
