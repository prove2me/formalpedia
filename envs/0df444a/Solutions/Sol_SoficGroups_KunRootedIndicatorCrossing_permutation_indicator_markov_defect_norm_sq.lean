-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.permutation_indicator_markov_defect_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/3bf0589a-591a-4789-920a-651ecbfd3960

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
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) :
    ‖permutationMarkov p (indicatorVector f) - indicatorVector f‖ ^ 2 =
      ∑ x, ((∑ i, f ((p i).symm x)) /
        (Fintype.card ι : ℝ) - f x) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro x _
  change ‖permutationMarkov p (indicatorVector f) x -
      indicatorVector f x‖ ^ 2 = _
  rw [permutationMarkov_apply]
  change ‖(∑ i, (f ((p i).symm x) : ℂ)) /
    (Fintype.card ι : ℂ) - (f x : ℂ)‖ ^ 2 = _
  have hcast :
      (∑ i, (f ((p i).symm x) : ℂ)) /
          (Fintype.card ι : ℂ) - (f x : ℂ) =
        (((∑ i, f ((p i).symm x)) /
          (Fintype.card ι : ℝ) - f x : ℝ) : ℂ) := by
    norm_cast
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, sq_abs]
end SoficGroups.KunRootedIndicatorCrossing
