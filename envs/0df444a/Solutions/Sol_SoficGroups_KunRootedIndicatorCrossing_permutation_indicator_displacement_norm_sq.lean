-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.permutation_indicator_displacement_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/36d689cb-580e-438d-b48d-60f7741f23a9

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
    {V : Type*} [Fintype V] (p : Equiv.Perm V) (f : V → ℝ) :
    ‖permutationUnitary p (indicatorVector f) - indicatorVector f‖ ^ 2 =
      ∑ x, (f (p.symm x) - f x) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro x _
  change ‖(f (p.symm x) : ℂ) - (f x : ℂ)‖ ^ 2 =
    (f (p.symm x) - f x) ^ 2
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]
end SoficGroups.KunRootedIndicatorCrossing
