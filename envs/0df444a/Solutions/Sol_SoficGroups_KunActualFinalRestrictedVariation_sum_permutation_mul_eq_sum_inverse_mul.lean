-- Prove2me | solution 1 for SoficGroups.KunActualFinalRestrictedVariation.sum_permutation_mul_eq_sum_inverse_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/32fb5f08-a3ea-48ef-b43c-d10326c1a423

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFinalRestrictedVariation
open scoped BigOperators
namespace SoficGroups.KunActualFinalRestrictedVariation
theorem _root_.solution
    {V : Type*} [Fintype V]
    (p : Equiv.Perm V) (f : V → ℝ) :
    (∑ x : V, f (p x) * f x) =
      ∑ x : V, f x * f (p.symm x) := by
  calc
    (∑ x : V, f (p x) * f x) =
        ∑ x : V, f (p (p.symm x)) * f (p.symm x) :=
      (Equiv.sum_comp p.symm
        (fun x : V => f (p x) * f x)).symm
    _ = ∑ x : V, f x * f (p.symm x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [p.apply_symm_apply]
end SoficGroups.KunActualFinalRestrictedVariation
