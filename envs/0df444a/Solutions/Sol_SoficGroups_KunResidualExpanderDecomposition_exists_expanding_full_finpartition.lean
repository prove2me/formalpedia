-- Prove2me | solution 1 for SoficGroups.KunResidualExpanderDecomposition.exists_expanding_full_finpartition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/c1939e01-3be3-49c4-a7f3-40cac92bcba5

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_exists_expanding_clean_finpartition
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_disjoint_clean_parts_singleton_bad_parts
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_sum_singleton_bad_boundary_le
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_completeCleanFinpartition_half_expansion

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
    ∃ P : Finpartition (Finset.univ : Finset V),
      (∀ C ∈ P.parts, ∀ E : Finset V, E ⊆ C →
        2 * E.card ≤ C.card →
          γ * (E.card : ℝ) ≤ (SoficGroups.boundary σ E : ℝ)) ∧
      (∑ C ∈ P.parts, (SoficGroups.boundary σ C : ℝ)) ≤
        2 * (Fintype.card ι : ℝ) * (B.card : ℝ) +
          4 * α * (Fintype.card V : ℝ) := by
  classical
  obtain ⟨Q, hQexpand, hQbudget⟩ :=
    exists_expanding_clean_finpartition σ B γ α hα himprove
  let P : Finpartition (Finset.univ : Finset V) :=
    completeCleanFinpartition B Q
  refine ⟨P, ?_, ?_⟩
  · exact completeCleanFinpartition_half_expansion
      σ B Q γ hQexpand
  · have hbad := sum_singleton_bad_boundary_le σ B
    have hdisjoint :=
      disjoint_clean_parts_singleton_bad_parts B Q
    have hclean :
        ((Finset.univ \ B).card : ℝ) ≤
          (Fintype.card V : ℝ) := by
      exact_mod_cast
        (Finset.card_le_card
          (Finset.sdiff_subset :
            Finset.univ \ B ⊆ (Finset.univ : Finset V)))
    have hscaled := mul_le_mul_of_nonneg_left hclean
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hα)
    calc
      (∑ C ∈ P.parts, (SoficGroups.boundary σ C : ℝ)) =
          (∑ C ∈ Q.parts, (SoficGroups.boundary σ C : ℝ)) +
            (∑ C ∈ (⊥ : Finpartition B).parts,
              (SoficGroups.boundary σ C : ℝ)) := by
                change
                  (∑ C ∈ (completeCleanFinpartition B Q).parts,
                    (SoficGroups.boundary σ C : ℝ)) = _
                rw [completeCleanFinpartition_parts,
                  Finset.sum_union hdisjoint]
      _ ≤ ((Fintype.card ι : ℝ) * (B.card : ℝ) +
            4 * α * ((Finset.univ \ B).card : ℝ)) +
          (Fintype.card ι : ℝ) * (B.card : ℝ) :=
            add_le_add hQbudget hbad
      _ ≤ 2 * (Fintype.card ι : ℝ) * (B.card : ℝ) +
          4 * α * (Fintype.card V : ℝ) := by
            nlinarith
end SoficGroups.KunResidualExpanderDecomposition
