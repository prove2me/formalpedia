-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.two_mul_mul_le_two_mul_sum_min_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:09:12.790473+00:00
-- url     : https://prove2.me/submissions/527769f6-04c6-4b52-b9e9-8a486766e92d

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Definitions.Def_SumOfSetsInSeveralDimensions_ClosedForm
public import Theorems.Thm_Finset_affineDim_empty
public import Theorems.Thm_Finset_affineDim_singleton
public import Theorems.Thm_Finset_affineDim_vadd_finset
attribute [local simp] Finset.affineDim_empty
attribute [local simp] Finset.affineDim_singleton
attribute [local simp] Finset.affineDim_vadd_finset


section
public section
namespace SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
private lemma sum_min_add_le {d k n : ℕ} (hkn : k + 2 ≤ n) :
    ∑ t ∈ Icc 1 k, min d (n - 1 - t) + (k + 1) ≤ ∑ t ∈ Icc 1 (k + 1), min (d + 1) (n - t) := by
  have h : ∑ t ∈ Icc 1 k, (min d (n - 1 - t) + 1) ≤ ∑ t ∈ Icc 1 k, min (d + 1) (n - t) := by
    apply sum_le_sum
    grind
  rw [sum_add_distrib, sum_const, Nat.card_Icc, smul_eq_mul] at h
  rw [sum_Icc_succ_top (by grind)]
  grind
private lemma two_mul_mul_succ_le {k d n : ℕ} (hn : k + 1 ≤ n) :
    2 * (d * (k + 1)) ≤ 2 * ∑ t ∈ Icc 1 k, min d (n - t) + d * (d + 1) := by
  induction k generalizing d n with
  | zero => grind [Nat.le_mul_self d]
  | succ k ih =>
    obtain _ | d := d
    · simp
    · grind [ih (d := d) (n := n - 1) (by grind), sum_min_add_le (d := d) hn]
variable {D d : ℕ} {A B : Finset (Fin D → ℝ)}
end SumOfSetsInSeveralDimensions
end
end

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution (d : ℕ) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    2 * (d * m) ≤ 2 * ∑ t ∈ Icc 1 (m - 1), min d (n - t) + d * (d + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one.2 hm
  exact two_mul_mul_succ_le hmn
end SumOfSetsInSeveralDimensions
