-- Prove2me | solution 1 for SoficGroups.KunDirectedIndicatorJensen.realPermutationMarkov_sub_sq_le_average_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/213a12dc-f3ef-4d54-bfd0-fb3eda1029d8

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunDirectedIndicatorJensen
open scoped BigOperators
namespace SoficGroups.KunDirectedIndicatorJensen
theorem _root_.solution
    {V ι : Type*} [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (x : V) :
    (realPermutationMarkov σ f x - f x) ^ 2 ≤
      (∑ i : ι,
        (f ((σ i).symm x) - f x) ^ 2) /
        (Fintype.card ι : ℝ) := by
  classical
  have hd : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty ι)
  have hmean :
      realPermutationMarkov σ f x - f x =
        (∑ i : ι, (f ((σ i).symm x) - f x)) /
          (Fintype.card ι : ℝ) := by
    unfold realPermutationMarkov
    rw [Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hcauchy :
      (∑ i : ι, (f ((σ i).symm x) - f x)) ^ 2 ≤
        (Fintype.card ι : ℝ) *
          ∑ i : ι, (f ((σ i).symm x) - f x) ^ 2 := by
    simpa only [Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq
        (s := Finset.univ)
        (f := fun i : ι => f ((σ i).symm x) - f x))
  rw [hmean, div_pow]
  calc
    (∑ i : ι, (f ((σ i).symm x) - f x)) ^ 2 /
        (Fintype.card ι : ℝ) ^ 2 ≤
      ((Fintype.card ι : ℝ) *
        ∑ i : ι, (f ((σ i).symm x) - f x) ^ 2) /
          (Fintype.card ι : ℝ) ^ 2 :=
        (div_le_div_iff_of_pos_right (sq_pos_of_pos hd)).mpr hcauchy
    _ = (∑ i : ι,
        (f ((σ i).symm x) - f x) ^ 2) /
          (Fintype.card ι : ℝ) := by
        field_simp
end SoficGroups.KunDirectedIndicatorJensen
