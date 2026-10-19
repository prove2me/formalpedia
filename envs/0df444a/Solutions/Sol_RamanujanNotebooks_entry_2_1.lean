-- Prove2me | solution 1 for RamanujanNotebooks.entry_2_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T14:26:04.200912+00:00
-- url     : https://prove2.me/submissions/41cde6f6-e76c-4684-b7b5-f0d5b416686c

import Mathlib

namespace RNE2

lemma step (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (1 : ℚ) / (((n + 1 : ℕ) : ℚ) + ((k : ℚ) + 1))) =
      (∑ k ∈ Finset.range n, (1 : ℚ) / ((n : ℚ) + ((k : ℚ) + 1))) - 1 / ((n : ℚ) + 1)
        + 1 / (2 * (n : ℚ) + 1) + 1 / (2 * (n : ℚ) + 2) := by
  have hB1 := Finset.sum_range_succ' (fun k : ℕ => (1 : ℚ) / ((n : ℚ) + ((k : ℚ) + 1))) n
  have hB2 := Finset.sum_range_succ (fun k : ℕ => (1 : ℚ) / ((n : ℚ) + ((k : ℚ) + 1))) n
  have hA := Finset.sum_range_succ (fun k : ℕ => (1 : ℚ) / (((n + 1 : ℕ) : ℚ) + ((k : ℚ) + 1))) n
  have hC : (∑ k ∈ Finset.range n, (1 : ℚ) / (((n + 1 : ℕ) : ℚ) + ((k : ℚ) + 1))) =
      ∑ k ∈ Finset.range n, (1 : ℚ) / ((n : ℚ) + (((k + 1 : ℕ) : ℚ) + 1)) := by
    apply Finset.sum_congr rfl; intro k _; push_cast; ring_nf
  rw [hA, hC]
  push_cast at hB1 hB2 ⊢
  have e1 : (1 : ℚ) / ((n : ℚ) + ((0 : ℚ) + 1)) = 1 / ((n : ℚ) + 1) := by ring_nf
  have e2 : (1 : ℚ) / ((n : ℚ) + ((n : ℚ) + 1)) = 1 / (2 * (n : ℚ) + 1) := by ring_nf
  have e3 : (1 : ℚ) / ((n : ℚ) + 1 + ((n : ℚ) + 1)) = 1 / (2 * (n : ℚ) + 2) := by ring_nf
  rw [e3]
  rw [e1] at hB1; rw [e2] at hB2
  linarith

theorem main (n : ℕ) :
    (∑ k ∈ Finset.range n, (1 : ℚ) / ((n : ℚ) + ((k : ℚ) + 1))) =
      (n : ℚ) / (2 * (n : ℚ) + 1) +
        (∑ k ∈ Finset.range n, (1 : ℚ) / ((2 * ((k : ℚ) + 1)) ^ 3 - 2 * ((k : ℚ) + 1))) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [step, ih, Finset.sum_range_succ]
    have h1 : (2 * ((m : ℚ) + 1)) ^ 3 - 2 * ((m : ℚ) + 1) = 2 * ((m : ℚ) + 1) * (2 * m + 1) * (2 * m + 3) := by ring
    rw [h1]
    push_cast
    field_simp
    ring

end RNE2

theorem solution (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.range n, (1 : ℚ) / ((n : ℚ) + ((k : ℚ) + 1))) =
      (n : ℚ) / (2 * (n : ℚ) + 1) +
        (∑ k ∈ Finset.range n, (1 : ℚ) / ((2 * ((k : ℚ) + 1)) ^ 3 - 2 * ((k : ℚ) + 1))) :=
  RNE2.main n
