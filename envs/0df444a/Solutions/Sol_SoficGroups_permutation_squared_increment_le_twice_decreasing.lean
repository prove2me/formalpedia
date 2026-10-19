-- Prove2me | solution 1 for SoficGroups.permutation_squared_increment_le_twice_decreasing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/fb9f487c-1cc5-4ba6-8859-e2d5ac9e0271

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_permutation_increment_sum_eq_zero

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {α : Type*} [Fintype α] (p : Equiv.Perm α) (f : α → ℝ)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le_one : ∀ x, f x ≤ 1) :
    ∑ x, (f (p x) - f x) ^ 2 ≤
      2 * ((Finset.univ.filter fun x => f (p x) < f x).card : ℝ) := by
  classical
  let d : α → ℝ := fun x => f (p x) - f x
  let B : Finset α := Finset.univ.filter fun x => d x < 0
  let C : Finset α := Finset.univ.filter fun x => ¬ d x < 0
  have hsum : ∑ x, d x = 0 :=
    permutation_increment_sum_eq_zero p f
  have hlower (x : α) : -1 ≤ d x := by
    dsimp [d]
    linarith [hf_nonneg (p x), hf_le_one x]
  have hupper (x : α) : d x ≤ 1 := by
    dsimp [d]
    linarith [hf_le_one (p x), hf_nonneg x]
  have hsplit : B.sum d + C.sum d = 0 := by
    calc
      B.sum d + C.sum d = ∑ x, d x := by
        simpa [B, C] using
          Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun x : α => d x < 0) d
      _ = 0 := hsum
  have habs_bad : B.sum (fun x => |d x|) = -(B.sum d) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have hneg : d x < 0 := (Finset.mem_filter.mp hx).2
    exact abs_of_neg hneg
  have habs_good : C.sum (fun x => |d x|) = C.sum d := by
    apply Finset.sum_congr rfl
    intro x hx
    have hnonneg : 0 ≤ d x :=
      le_of_not_gt (Finset.mem_filter.mp hx).2
    exact abs_of_nonneg hnonneg
  have habs_split :
      B.sum (fun x => |d x|) + C.sum (fun x => |d x|) =
        ∑ x, |d x| := by
    simpa [B, C] using
      Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun x : α => d x < 0) (fun x => |d x|)
  have habs_total : (∑ x, |d x|) = -2 * B.sum d := by
    rw [← habs_split, habs_bad, habs_good]
    linarith
  have hbad : -(B.sum d) ≤ (B.card : ℝ) := by
    calc
      -(B.sum d) = B.sum (fun x => -d x) := by
        simp
      _ ≤ B.sum (fun _ => (1 : ℝ)) := by
        apply Finset.sum_le_sum
        intro x _
        linarith [hlower x]
      _ = (B.card : ℝ) := by simp
  have hsquare : (∑ x, d x ^ 2) ≤ ∑ x, |d x| := by
    apply Finset.sum_le_sum
    intro x _
    by_cases h : 0 ≤ d x
    · rw [abs_of_nonneg h]
      nlinarith [hupper x]
    · have hneg : d x < 0 := lt_of_not_ge h
      rw [abs_of_neg hneg]
      nlinarith [hlower x]
  rw [habs_total] at hsquare
  have hfinal : (∑ x, d x ^ 2) ≤ 2 * (B.card : ℝ) := by
    linarith
  simpa [d, B, sub_neg] using hfinal
end SoficGroups
