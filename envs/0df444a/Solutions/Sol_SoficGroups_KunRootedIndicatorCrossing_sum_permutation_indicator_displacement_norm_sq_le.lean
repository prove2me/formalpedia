-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.sum_permutation_indicator_displacement_norm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/0f3bf9f7-3a5a-4e80-a8b8-b07081df31ab

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_sum_sum_indicator_displacement_sq_le_card_sq_mul_markov_defect
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_permutation_indicator_displacement_norm_sq
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_permutation_indicator_markov_defect_norm_sq

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {ι V : Type*} [Fintype ι] [Nonempty ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1) :
    (∑ i, ‖permutationUnitary (p i) (indicatorVector f) -
      indicatorVector f‖ ^ 2) ≤
        (Fintype.card ι : ℝ) ^ 2 *
          ‖permutationMarkov p (indicatorVector f) -
            indicatorVector f‖ ^ 2 := by
  simp_rw [permutation_indicator_displacement_norm_sq,
    permutation_indicator_markov_defect_norm_sq]
  exact sum_sum_indicator_displacement_sq_le_card_sq_mul_markov_defect
    (fun i x => (p i).symm x) f hf
end SoficGroups.KunRootedIndicatorCrossing
