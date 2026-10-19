-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.sum_sum_indicator_displacement_sq_le_card_sq_mul_markov_defect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/e9a82c54-798a-448d-a67d-043b91eed8f4

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_sum_sum_indicator_displacement_sq_le

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
    (p : ι → V → V) (f : V → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1) :
    (∑ i, ∑ x, (f (p i x) - f x) ^ 2) ≤
      (Fintype.card ι : ℝ) ^ 2 *
        ∑ x, ((∑ i, f (p i x)) / (Fintype.card ι : ℝ) - f x) ^ 2 := by
  have hd : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hpoint (x : V) :
      (Fintype.card ι : ℝ) ^ 2 *
          ((∑ i, f (p i x)) / (Fintype.card ι : ℝ) - f x) ^ 2 =
        (∑ i, (f (p i x) - f x)) ^ 2 := by
    rw [← mul_pow]
    congr 1
    rw [mul_sub, mul_div_cancel₀ _ hd, Finset.sum_sub_distrib]
    simp [mul_comm]
  calc
    (∑ i, ∑ x, (f (p i x) - f x) ^ 2) ≤
        ∑ x, (∑ i, (f (p i x) - f x)) ^ 2 :=
      sum_sum_indicator_displacement_sq_le p f hf
    _ = (Fintype.card ι : ℝ) ^ 2 *
        ∑ x, ((∑ i, f (p i x)) / (Fintype.card ι : ℝ) - f x) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => (hpoint x).symm
end SoficGroups.KunRootedIndicatorCrossing
