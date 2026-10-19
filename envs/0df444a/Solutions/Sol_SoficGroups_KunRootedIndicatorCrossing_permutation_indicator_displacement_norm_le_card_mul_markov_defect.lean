-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.permutation_indicator_displacement_norm_le_card_mul_markov_defect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/d4b2d372-1a64-4f3c-870b-9499e2d86750

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_sum_permutation_indicator_displacement_norm_sq_le

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
    (hf : ∀ x, f x = 0 ∨ f x = 1) (i : ι) :
    ‖permutationUnitary (p i) (indicatorVector f) - indicatorVector f‖ ≤
      (Fintype.card ι : ℝ) *
        ‖permutationMarkov p (indicatorVector f) - indicatorVector f‖ := by
  have hsingle :
      ‖permutationUnitary (p i) (indicatorVector f) -
        indicatorVector f‖ ^ 2 ≤
        ∑ j, ‖permutationUnitary (p j) (indicatorVector f) -
          indicatorVector f‖ ^ 2 :=
    Finset.single_le_sum
      (f := fun j : ι =>
        ‖permutationUnitary (p j) (indicatorVector f) -
          indicatorVector f‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have htotal :=
    sum_permutation_indicator_displacement_norm_sq_le p f hf
  have hsq :
      ‖permutationUnitary (p i) (indicatorVector f) -
        indicatorVector f‖ ^ 2 ≤
        ((Fintype.card ι : ℝ) *
          ‖permutationMarkov p (indicatorVector f) -
            indicatorVector f‖) ^ 2 := by
    rw [mul_pow]
    exact hsingle.trans htotal
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity)
    (norm_nonneg _))).mp hsq
end SoficGroups.KunRootedIndicatorCrossing
