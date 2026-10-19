-- Prove2me | solution 1 for SoficGroups.KunDirectedIndicatorJensen.sum_sum_sq_realIndicator_inverse_displacement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/3f009e56-dcf6-48f8-a6aa-02980e64f526

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunDirectedIndicatorJensen_sum_sq_realIndicator_inverse_displacement

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunDirectedIndicatorJensen
open scoped BigOperators
namespace SoficGroups.KunDirectedIndicatorJensen
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (T : Finset V) :
    (∑ i : ι, ∑ x : V,
      (realIndicator T ((σ i).symm x) - realIndicator T x) ^ 2) =
      2 * (SoficGroups.boundary σ T : ℝ) := by
  classical
  simp_rw [sum_sq_realIndicator_inverse_displacement]
  unfold SoficGroups.boundary
  push_cast
  rw [Finset.mul_sum]
end SoficGroups.KunDirectedIndicatorJensen
