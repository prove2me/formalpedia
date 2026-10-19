-- Prove2me | solution 1 for SoficGroups.norm_finset_sum_sq_eq_of_pairwise_inner_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/e01d3ff3-000b-42d6-86a9-5cb94ccde9dd

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u₁ v₁
namespace SoficGroups
theorem _root_.solution
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (f : ι → H) (s : Finset ι)
    (horth : ∀ ⦃i j : ι⦄, i ≠ j → inner ℂ (f i) (f j) = 0) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [norm_add_sq (𝕜 := ℂ)]
      have hzero : inner ℂ (f i) (∑ j ∈ s, f j) = 0 := by
        rw [inner_sum]
        apply Finset.sum_eq_zero
        intro j hj
        exact horth (by
          intro h
          subst j
          exact hi hj)
      simp [hzero, ih]
end SoficGroups
