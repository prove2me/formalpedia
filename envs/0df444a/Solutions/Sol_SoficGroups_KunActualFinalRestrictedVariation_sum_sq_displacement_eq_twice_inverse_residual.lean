-- Prove2me | solution 1 for SoficGroups.KunActualFinalRestrictedVariation.sum_sq_displacement_eq_twice_inverse_residual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/9fe9ad24-ba22-4005-8f10-55199508b8ce

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualFinalRestrictedVariation_sum_permutation_mul_eq_sum_inverse_mul

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFinalRestrictedVariation
open scoped BigOperators
namespace SoficGroups.KunActualFinalRestrictedVariation
theorem _root_.solution
    {V : Type*} [Fintype V]
    (p : Equiv.Perm V) (f : V → ℝ) :
    (∑ x : V, (f (p x) - f x) ^ 2) =
      2 * ∑ x : V, f x * (f x - f (p.symm x)) := by
  have hsquare :
      (∑ x : V, f (p x) ^ 2) = ∑ x : V, f x ^ 2 :=
    Equiv.sum_comp p (fun x : V => f x ^ 2)
  have hcross := sum_permutation_mul_eq_sum_inverse_mul p f
  calc
    (∑ x : V, (f (p x) - f x) ^ 2) =
        (∑ x : V, f (p x) ^ 2) +
          (∑ x : V, f x ^ 2) -
            2 * ∑ x : V, f (p x) * f x := by
      calc
        (∑ x : V, (f (p x) - f x) ^ 2) =
            ∑ x : V,
              (f (p x) ^ 2 + f x ^ 2 -
                2 * (f (p x) * f x)) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
        _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum]
    _ = 2 * ∑ x : V, f x * (f x - f (p.symm x)) := by
      rw [hsquare, hcross]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      ring_nf
end SoficGroups.KunActualFinalRestrictedVariation
