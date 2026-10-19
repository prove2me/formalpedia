-- Prove2me | solution 1 for SoficGroups.KunActualFinalRestrictedVariation.sum_sum_sq_displacement_eq_twice_card_mul_realMarkov_residual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/efbb1ee8-d9c0-4104-93ed-0402ef40c0a2

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualFinalRestrictedVariation_sum_sq_displacement_eq_twice_inverse_residual

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFinalRestrictedVariation
open scoped BigOperators
namespace SoficGroups.KunActualFinalRestrictedVariation
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) :
    (∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2) =
      2 * (Fintype.card ι : ℝ) *
        ∑ x : V, f x * (f x - realMarkov σ f x) := by
  classical
  have hd : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty ι)
  calc
    (∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2) =
        2 * ∑ x : V, ∑ i : ι,
          f x * (f x - f ((σ i).symm x)) := by
      simp_rw [sum_sq_displacement_eq_twice_inverse_residual]
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ = 2 * (Fintype.card ι : ℝ) *
        ∑ x : V, f x * (f x - realMarkov σ f x) := by
      rw [mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      unfold realMarkov
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      field_simp
end SoficGroups.KunActualFinalRestrictedVariation
