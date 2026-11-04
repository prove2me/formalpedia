-- Prove2me | solution 1 for ThreeSum.SparseBoxes.sparse_query_identity_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:41:05.672375+00:00
-- url     : https://prove2.me/submissions/a11bf9df-9603-4f5c-94a6-50c2f2e3b052

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_SparseBoxes
import Theorems.Thm_ThreeSum_SparseBoxes_queryBox_partition
import Theorems.Thm_ThreeSum_SparseBoxes_no_queryBox_of_few_missing
import Theorems.Thm_ThreeSum_SparseBoxes_boxSum_extend
namespace ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
private theorem query_fiber_sum (q leaf : Finset α) (t : ℕ)
    (weight : Finset α → ℤ) (hl : leaf ∈ q.powerset) :
    (∑ u ∈ q.powersetCard t, if QueryBox q u leaf then weight leaf else 0) =
      if (q \ leaf).card < t then 0 else weight leaf := by
  by_cases hs : (q \ leaf).card < t
  · simp only [hs, ite_true]
    apply Finset.sum_eq_zero
    intro u hu
    simp only [no_queryBox_of_few_missing q leaf u t hu hs, ite_false]
  · have ht : t ≤ (q \ leaf).card := by omega
    obtain ⟨u, hu, huniq⟩ := queryBox_partition q leaf t (Finset.mem_powerset.mp hl) ht
    rw [Finset.sum_eq_single u]
    · simp [hu.2, hs]
    · intro v hv hvn
      have hn : ¬ QueryBox q v leaf := by
        intro hb
        exact hvn (huniq v ⟨hv, hb⟩)
      simp only [hn, ite_false]
    · intro h
      exact False.elim (h hu.1)
end ThreeSum.SparseBoxes
set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
namespace ThreeSum.SparseBoxes
theorem _root_.solution (q : Finset α) (t : ℕ) (weight : Finset α → ℤ) :
    (∑ leaf ∈ q.powerset, weight leaf) =
      (∑ leaf ∈ q.powerset with (q \ leaf).card < t, weight leaf) +
      ∑ u ∈ q.powersetCard t, boxSum (q \ u) (queryFree q u) weight := by
  have hboxes :
      (∑ u ∈ q.powersetCard t, boxSum (q \ u) (queryFree q u) weight) =
      ∑ leaf ∈ q.powerset, if (q \ leaf).card < t then 0 else weight leaf := by
    calc
      _ = ∑ u ∈ q.powersetCard t, ∑ leaf ∈ q.powerset,
            if QueryBox q u leaf then weight leaf else 0 := by
        apply Finset.sum_congr rfl
        intro u hu
        exact boxSum_extend q (q \ u) (queryFree q u) weight Finset.sdiff_subset
      _ = ∑ leaf ∈ q.powerset, ∑ u ∈ q.powersetCard t,
            if QueryBox q u leaf then weight leaf else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro leaf hl
        exact query_fiber_sum q leaf t weight hl
  rw [hboxes, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro leaf hl
  by_cases h : (q \ leaf).card < t <;> simp [h]
end ThreeSum.SparseBoxes
