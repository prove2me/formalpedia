-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.sum_indicator_displacement_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/d8c2966b-4591-4293-a76c-6e6eacb4b3a9

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_sum_sq_le_sq_sum_of_same_sign
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_indicator_displacements_same_sign

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {ι V : Type*} [Fintype ι] (p : ι → V → V) (f : V → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1) (x : V) :
    (∑ i, (f (p i x) - f x) ^ 2) ≤
      (∑ i, (f (p i x) - f x)) ^ 2 :=
  sum_sq_le_sq_sum_of_same_sign _
    (indicator_displacements_same_sign p f hf x)
end SoficGroups.KunRootedIndicatorCrossing
