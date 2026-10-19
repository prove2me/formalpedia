-- Prove2me | solution 1 for SoficGroups.KunResidualExpanderDecomposition.boundary_inter_add_boundary_sdiff_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/670266da-996f-4ee1-8366-edf0d78df4aa

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_boundary_eq_sum_indicator
import Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_boundary_eq_sum_entering_indicator

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualExpanderDecomposition
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.KunResidualExpanderDecomposition
theorem _root_.solution {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (R U : Finset V) :
    SoficGroups.boundary σ (R ∩ U) +
        SoficGroups.boundary σ (R \ U) ≤
      SoficGroups.boundary σ R + 2 * SoficGroups.boundary σ U := by
  classical
  have hpoint (i : ι) (x : V) :
      (if x ∈ R ∩ U ∧ σ i x ∉ R ∩ U then 1 else 0) +
          (if x ∈ R \ U ∧ σ i x ∉ R \ U then 1 else 0) ≤
        (if x ∈ R ∧ σ i x ∉ R then 1 else 0) +
          (if x ∈ U ∧ σ i x ∉ U then 1 else 0) +
          (if x ∉ U ∧ σ i x ∈ U then 1 else 0) := by
    by_cases hxR : x ∈ R <;>
      by_cases hxU : x ∈ U <;>
      by_cases hyR : σ i x ∈ R <;>
      by_cases hyU : σ i x ∈ U <;>
      simp [hxR, hxU, hyR, hyU]
  calc
    SoficGroups.boundary σ (R ∩ U) +
        SoficGroups.boundary σ (R \ U) =
      ∑ i : ι, ∑ x : V,
        ((if x ∈ R ∩ U ∧ σ i x ∉ R ∩ U then 1 else 0) +
         (if x ∈ R \ U ∧ σ i x ∉ R \ U then 1 else 0)) := by
          rw [boundary_eq_sum_indicator, boundary_eq_sum_indicator]
          simp_rw [Finset.sum_add_distrib]
    _ ≤ ∑ i : ι, ∑ x : V,
        ((if x ∈ R ∧ σ i x ∉ R then 1 else 0) +
         (if x ∈ U ∧ σ i x ∉ U then 1 else 0) +
         (if x ∉ U ∧ σ i x ∈ U then 1 else 0)) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro x _
          exact hpoint i x
    _ = SoficGroups.boundary σ R +
        2 * SoficGroups.boundary σ U := by
          rw [boundary_eq_sum_indicator σ R,
            boundary_eq_sum_indicator σ U]
          have henter := boundary_eq_sum_entering_indicator σ U
          rw [boundary_eq_sum_indicator σ U] at henter
          simp_rw [Finset.sum_add_distrib]
          omega
end SoficGroups.KunResidualExpanderDecomposition
