-- Prove2me | solution 1 for SoficGroups.KunRealComplexMarkovBridge.norm_indicatorVector_sub_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/57c96523-f679-4965-941a-a98d2037d696

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRealComplexMarkovBridge
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRealComplexMarkovBridge
theorem _root_.solution
    {V : Type*} [Fintype V] (f g : V → ℝ) :
    ‖indicatorVector f - indicatorVector g‖ ^ 2 =
      ∑ x, (f x - g x) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro x _
  change ‖(f x : ℂ) - (g x : ℂ)‖ ^ 2 = (f x - g x) ^ 2
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
end SoficGroups.KunRealComplexMarkovBridge
