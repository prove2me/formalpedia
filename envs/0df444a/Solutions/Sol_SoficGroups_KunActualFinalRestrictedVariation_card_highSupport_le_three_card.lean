-- Prove2me | solution 1 for SoficGroups.KunActualFinalRestrictedVariation.card_highSupport_le_three_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/e9f8ece0-282c-404d-bed3-1fa8b2c9ae51

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFinalRestrictedVariation
open scoped BigOperators
namespace SoficGroups.KunActualFinalRestrictedVariation
theorem _root_.solution
    {V : Type*} [Fintype V]
    (T : Finset V) (f : V → ℝ)
    (hfzero : ∀ x, 0 ≤ f x)
    (hmass : (∑ x : V, f x) = (T.card : ℝ)) :
    (((Finset.univ.filter fun x : V =>
      (1 / 3 : ℝ) < f x).card : ℝ)) ≤ 3 * (T.card : ℝ) := by
  classical
  let H : Finset V :=
    Finset.univ.filter fun x : V => (1 / 3 : ℝ) < f x
  have hpoint (x : V) (hx : x ∈ H) :
      (1 : ℝ) ≤ 3 * f x := by
    have hx' : (1 / 3 : ℝ) < f x :=
      (Finset.mem_filter.mp hx).2
    linarith
  have hhigh : (H.card : ℝ) ≤ 3 * ∑ x ∈ H, f x := by
    calc
      (H.card : ℝ) = ∑ _x ∈ H, (1 : ℝ) := by simp
      _ ≤ ∑ x ∈ H, 3 * f x :=
        Finset.sum_le_sum fun x hx => hpoint x hx
      _ = 3 * ∑ x ∈ H, f x := by rw [Finset.mul_sum]
  have hsum : (∑ x ∈ H, f x) ≤ ∑ x : V, f x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ H)
    intro x _ _
    exact hfzero x
  change (H.card : ℝ) ≤ 3 * (T.card : ℝ)
  calc
    (H.card : ℝ) ≤ 3 * ∑ x ∈ H, f x := hhigh
    _ ≤ 3 * ∑ x : V, f x :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 3 * (T.card : ℝ) := by rw [hmass]
end SoficGroups.KunActualFinalRestrictedVariation
