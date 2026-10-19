-- Prove2me | solution 1 for SoficGroups.KunResidualExpanderDecomposition.sum_singleton_bad_boundary_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/8b408982-3630-474e-8e8f-d26caf9fc2a0

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_boundary_le_degree_mul_card

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualExpanderDecomposition
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.KunResidualExpanderDecomposition
theorem _root_.solution
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B : Finset V) :
    (∑ C ∈ (⊥ : Finpartition B).parts,
      (SoficGroups.boundary σ C : ℝ)) ≤
        (Fintype.card ι : ℝ) * (B.card : ℝ) := by
  classical
  calc
    (∑ C ∈ (⊥ : Finpartition B).parts,
      (SoficGroups.boundary σ C : ℝ)) =
        ∑ x ∈ B, (SoficGroups.boundary σ {x} : ℝ) := by
          simp [Finpartition.parts_bot]
    _ ≤ ∑ _x ∈ B, (Fintype.card ι : ℝ) := by
          apply Finset.sum_le_sum
          intro x _
          have h := boundary_le_degree_mul_card σ ({x} : Finset V)
          have h' :
              SoficGroups.boundary σ ({x} : Finset V) ≤
                Fintype.card ι := by
            simpa only [Finset.card_singleton, mul_one] using h
          exact_mod_cast h'
    _ = (Fintype.card ι : ℝ) * (B.card : ℝ) := by
          simp [mul_comm]
end SoficGroups.KunResidualExpanderDecomposition
