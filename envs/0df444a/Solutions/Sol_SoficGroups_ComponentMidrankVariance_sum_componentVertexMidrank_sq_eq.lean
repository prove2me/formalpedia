-- Prove2me | solution 1 for SoficGroups.ComponentMidrankVariance.sum_componentVertexMidrank_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/0513d187-5d63-4370-ab5c-0d109b267622

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_sum_componentRankMass
import Theorems.Thm_SoficGroups_ComponentMidrankVariance_sum_weighted_ordered_midpoints_sq
import Theorems.Thm_SoficGroups_ComponentMidrankVariance_componentVertexMidrank_eq_ordered_midpoint

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
    (∑ x ∈ C, SoficGroups.componentVertexMidrank C b x ^ 2) =
      (C.card : ℝ) *
        ((1 : ℝ) / 3 -
          (∑ j ∈ C.image b, SoficGroups.componentRankMass C b j ^ 3) / 12) := by
  classical
  have hcard : (C.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hC
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := C) (t := C.image b) (g := b)
    (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    (fun x => SoficGroups.componentVertexMidrank C b x ^ 2)
  calc
    (∑ x ∈ C, SoficGroups.componentVertexMidrank C b x ^ 2) =
        ∑ j ∈ C.image b,
          ∑ x ∈ C.filter (fun x => b x = j),
            SoficGroups.componentVertexMidrank C b x ^ 2 := hfiber.symm
    _ = ∑ j ∈ C.image b,
          ((C.filter fun x => b x = j).card : ℝ) *
            (lowerRankWeight (C.image b) (SoficGroups.componentRankMass C b) j +
              SoficGroups.componentRankMass C b j / 2) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          calc
            (∑ x ∈ C.filter (fun x => b x = j),
                SoficGroups.componentVertexMidrank C b x ^ 2) =
              ∑ _x ∈ C.filter (fun x => b x = j),
                (lowerRankWeight (C.image b) (SoficGroups.componentRankMass C b) j +
                  SoficGroups.componentRankMass C b j / 2) ^ 2 := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    have hbx : b x = j := (Finset.mem_filter.mp hx).2
                    rw [componentVertexMidrank_eq_ordered_midpoint C b x, hbx]
            _ = ((C.filter fun x => b x = j).card : ℝ) *
                (lowerRankWeight (C.image b) (SoficGroups.componentRankMass C b) j +
                  SoficGroups.componentRankMass C b j / 2) ^ 2 := by
                    simp
    _ = (C.card : ℝ) *
          (∑ j ∈ C.image b,
            SoficGroups.componentRankMass C b j *
              (lowerRankWeight (C.image b) (SoficGroups.componentRankMass C b) j +
                SoficGroups.componentRankMass C b j / 2) ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          have hweight :
              ((C.filter fun x => b x = j).card : ℝ) =
                (C.card : ℝ) * SoficGroups.componentRankMass C b j := by
            unfold SoficGroups.componentRankMass
            field_simp
          rw [hweight]
          ring
    _ = (C.card : ℝ) *
          (((∑ j ∈ C.image b, SoficGroups.componentRankMass C b j) ^ 3 / 3) -
            (∑ j ∈ C.image b, SoficGroups.componentRankMass C b j ^ 3) / 12) := by
          rw [sum_weighted_ordered_midpoints_sq]
    _ = (C.card : ℝ) *
          ((1 : ℝ) / 3 -
            (∑ j ∈ C.image b, SoficGroups.componentRankMass C b j ^ 3) / 12) := by
          rw [SoficGroups.sum_componentRankMass C b hC]
          norm_num
end SoficGroups.ComponentMidrankVariance
