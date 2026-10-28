-- Prove2me | solution 1 for TaoFivePrimes.nonnegative_weight_bin_cover_65000
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:07:03.240205+00:00
-- url     : https://prove2.me/submissions/46dcfbdb-ec54-4fd2-a5d7-527f2f118183

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Finset

private lemma interval_cover (t : ℝ) (hlo : 65000 < t) :
    ∀ n : ℕ, t ≤ 65000+1290*(n:ℝ) →
      ∃ i ∈ Finset.range n,
        65000+1290*(i:ℝ) < t ∧ t ≤ 65000+1290*((i:ℝ)+1) := by
  intro n
  induction n with
  | zero =>
    intro ht
    norm_num at ht
    linarith
  | succ n ih =>
    intro ht
    by_cases hn : t ≤ 65000+1290*(n:ℝ)
    · obtain ⟨i, hi, hleft, hright⟩ := ih hn
      refine ⟨i, Finset.mem_range.mpr ?_, hleft, hright⟩
      have : i < n := Finset.mem_range.mp hi
      omega
    · refine ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), ?_, ?_⟩
      · exact lt_of_not_ge hn
      · push_cast at ht
        linarith

theorem solution {α : Type*} [DecidableEq α] (S : Finset α) (γ w : α → ℝ)
    (hw : ∀ x ∈ S, 0 ≤ w x)
    (hlo : ∀ x ∈ S, 65000 < γ x)
    (hhi : ∀ x ∈ S, γ x ≤ 297200) :
    (∑ x ∈ S, w x) ≤
      ∑ i ∈ Finset.range 180,
        ∑ x ∈ S.filter (fun x => 65000+1290*(i:ℝ) < γ x ∧
          γ x ≤ 65000+1290*((i:ℝ)+1)), w x := by
  classical
  calc
    _ ≤ ∑ x ∈ S, ∑ i ∈ Finset.range 180,
        if 65000+1290*(i:ℝ) < γ x ∧ γ x ≤ 65000+1290*((i:ℝ)+1) then w x else 0 := by
      apply Finset.sum_le_sum
      intro x hx
      have ht : γ x ≤ 65000+1290*(180:ℝ) := by norm_num; exact hhi x hx
      obtain ⟨i, hi, hleft, hright⟩ := interval_cover (γ x) (hlo x hx) 180 ht
      have hnonneg (j : ℕ) (hj : j ∈ Finset.range 180) :
          0 ≤ (if 65000+1290*(j:ℝ) < γ x ∧ γ x ≤ 65000+1290*((j:ℝ)+1)
            then w x else 0) := by
        split_ifs
        · exact hw x hx
        · exact le_rfl
      calc
        w x = (if 65000+1290*(i:ℝ) < γ x ∧ γ x ≤ 65000+1290*((i:ℝ)+1) then w x else 0) := by
          simp [hleft,hright]
        _ ≤ _ := Finset.single_le_sum hnonneg hi
    _ = ∑ i ∈ Finset.range 180, ∑ x ∈ S,
        if 65000+1290*(i:ℝ) < γ x ∧ γ x ≤ 65000+1290*((i:ℝ)+1) then w x else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_filter]
