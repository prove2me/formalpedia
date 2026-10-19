-- Prove2me | solution 1 for SoficGroups.ComponentMidrankVariance.componentVertexMidrank_variance_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/3c5ea30d-450e-4792-ba85-8c462b615098

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_midrankVariance_eq
import Theorems.Thm_SoficGroups_componentRankMassList_sum
import Theorems.Thm_SoficGroups_ComponentMidrankVariance_sum_componentVertexMidrank
import Theorems.Thm_SoficGroups_ComponentMidrankVariance_sum_componentVertexMidrank_sq_eq
import Theorems.Thm_SoficGroups_ComponentMidrankVariance_componentRankMassList_cube_sum

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.ComponentMidrankVariance
open scoped BigOperators
namespace SoficGroups.ComponentMidrankVariance
theorem _root_.solution
    {V : Type*}
    (C : Finset V) (b : V → ℤ) (hC : C.Nonempty) :
    (∑ x ∈ C,
      (SoficGroups.componentVertexMidrank C b x - (1 / 2 : ℝ)) ^ 2) =
      (C.card : ℝ) *
        SoficGroups.midrankVariance (SoficGroups.componentRankMassList C b) := by
  have hcenter :
      (∑ x ∈ C,
        (SoficGroups.componentVertexMidrank C b x - (1 / 2 : ℝ)) ^ 2) =
        (∑ x ∈ C, SoficGroups.componentVertexMidrank C b x ^ 2) -
          (∑ x ∈ C, SoficGroups.componentVertexMidrank C b x) +
          (C.card : ℝ) / 4 := by
    calc
      (∑ x ∈ C,
        (SoficGroups.componentVertexMidrank C b x - (1 / 2 : ℝ)) ^ 2) =
          ∑ x ∈ C,
            (SoficGroups.componentVertexMidrank C b x ^ 2 -
              SoficGroups.componentVertexMidrank C b x + (1 / 4 : ℝ)) := by
                apply Finset.sum_congr rfl
                intro x _
                ring
      _ = (∑ x ∈ C, SoficGroups.componentVertexMidrank C b x ^ 2) -
          (∑ x ∈ C, SoficGroups.componentVertexMidrank C b x) +
          (C.card : ℝ) / 4 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            simp [div_eq_mul_inv]
  calc
    (∑ x ∈ C,
      (SoficGroups.componentVertexMidrank C b x - (1 / 2 : ℝ)) ^ 2) =
        (C.card : ℝ) *
            ((1 : ℝ) / 3 -
              (∑ j ∈ C.image b,
                SoficGroups.componentRankMass C b j ^ 3) / 12) -
          (C.card : ℝ) / 2 + (C.card : ℝ) / 4 := by
            rw [hcenter, sum_componentVertexMidrank_sq_eq C b hC,
              sum_componentVertexMidrank C b hC]
    _ = (C.card : ℝ) *
        SoficGroups.midrankVariance (SoficGroups.componentRankMassList C b) := by
          rw [SoficGroups.midrankVariance_eq
            (SoficGroups.componentRankMassList C b)
            (SoficGroups.componentRankMassList_sum C b hC),
            componentRankMassList_cube_sum C b]
          ring
end SoficGroups.ComponentMidrankVariance
