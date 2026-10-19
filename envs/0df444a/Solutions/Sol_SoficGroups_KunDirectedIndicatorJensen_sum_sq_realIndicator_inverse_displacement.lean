-- Prove2me | solution 1 for SoficGroups.KunDirectedIndicatorJensen.sum_sq_realIndicator_inverse_displacement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/f5d6268e-e027-4b49-9659-9ece15cdd62d

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunDirectedIndicatorJensen_sum_sq_realIndicator_displacement

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunDirectedIndicatorJensen
open scoped BigOperators
namespace SoficGroups.KunDirectedIndicatorJensen
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (T : Finset V) :
    (∑ x : V,
      (realIndicator T (p.symm x) - realIndicator T x) ^ 2) =
      2 * ((T.filter fun x => p x ∉ T).card : ℝ) := by
  classical
  calc
    (∑ x : V,
      (realIndicator T (p.symm x) - realIndicator T x) ^ 2) =
        ∑ x : V,
          (realIndicator T (p.symm (p x)) -
            realIndicator T (p x)) ^ 2 := by
          exact (Equiv.sum_comp p
            (fun x : V =>
              (realIndicator T (p.symm x) - realIndicator T x) ^ 2)).symm
    _ = ∑ x : V,
          (realIndicator T (p x) - realIndicator T x) ^ 2 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [p.symm_apply_apply]
          ring
    _ = 2 * ((T.filter fun x => p x ∉ T).card : ℝ) :=
      sum_sq_realIndicator_displacement p T
end SoficGroups.KunDirectedIndicatorJensen
