-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.sum_sq_le_sq_sum_of_same_sign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/1170297e-c615-4fde-a9c9-493e0d5e3e96

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (h : (∀ i, 0 ≤ a i) ∨ (∀ i, a i ≤ 0)) :
    (∑ i, a i ^ 2) ≤ (∑ i, a i) ^ 2 := by
  rcases h with h | h
  · exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => h i)
  · have hn := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := Finset.univ) (f := fun i : ι => -a i)
      (fun i _ => neg_nonneg.mpr (h i))
    simpa [sq] using hn
end SoficGroups.KunRootedIndicatorCrossing
