-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.sum_sum_indicator_displacement_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/b3e73fca-e089-4254-9121-813d36b09e36

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_sum_indicator_displacement_sq_le

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → V → V) (f : V → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1) :
    (∑ i, ∑ x, (f (p i x) - f x) ^ 2) ≤
      ∑ x, (∑ i, (f (p i x) - f x)) ^ 2 := by
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun x _ =>
    sum_indicator_displacement_sq_le p f hf x
end SoficGroups.KunRootedIndicatorCrossing
