-- Prove2me | solution 1 for SoficGroups.permutation_increment_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/b9d54e4d-3d5c-4e02-8159-56296150e96a

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {α : Type*} [Fintype α] (p : Equiv.Perm α) (f : α → ℝ) :
    ∑ x, (f (p x) - f x) = 0 := by
  rw [Finset.sum_sub_distrib, Equiv.sum_comp p f]
  exact sub_self _
end SoficGroups
