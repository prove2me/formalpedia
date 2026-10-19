-- Prove2me | solution 2 for RamanujanNotebooks.entry_2_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:15:51.694562+00:00
-- url     : https://prove2.me/submissions/fa2b754a-eb92-4698-9808-ad12071609b7

import Mathlib
set_option autoImplicit false

lemma ram_shift (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (1 : ℚ) / (((n + 1 : ℕ) : ℚ) + ((k : ℚ) + 1))) =
      (∑ k ∈ Finset.range n, (1 : ℚ) / ((n : ℚ) + ((k : ℚ) + 1))) + 1 / (2 * (n : ℚ) + 1)
        - 1 / (2 * (n : ℚ) + 2) := by
  have h1 : (∑ k ∈ Finset.range (n + 1), (1 : ℚ) / ((n : ℚ) + ((k : ℚ) + 1))) =
      (∑ k ∈ Finset.range n, (1 : ℚ) / ((n : ℚ) + ((k : ℚ) + 1))) + 1 / (2 * (n : ℚ) + 1) := by
    rw [Finset.sum_range_succ]
    congr 1
    ring_nf
  have h2 : (∑ k ∈ Finset.range (n + 1), (1 : ℚ) / ((n : ℚ) + ((k : ℚ) + 1))) =
      1 / ((n : ℚ) + 1) +
      ∑ k ∈ Finset.range n, (1 : ℚ) / ((n : ℚ) + (((k + 1 : ℕ) : ℚ) + 1)) := by
    rw [Finset.sum_range_succ']
    simp [add_comm]
  have h3 : (∑ k ∈ Finset.range (n + 1), (1 : ℚ) / (((n + 1 : ℕ) : ℚ) + ((k : ℚ) + 1))) =
      (∑ k ∈ Finset.range n, (1 : ℚ) / ((n : ℚ) + (((k + 1 : ℕ) : ℚ) + 1))) + 1 / (2 * (n : ℚ) + 2) := by
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro k _
      push_cast
      congr 1
      ring
    · push_cast
      congr 1
      ring
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  have h4 : 1 / ((n : ℚ) + 1) = 2 * (1 / (2 * (n : ℚ) + 2)) := by
    field_simp
  rw [h3]
  linarith [h1, h2, h4]

theorem solution (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.range n, (1 : ℚ) / ((n : ℚ) + ((k : ℚ) + 1))) =
      (n : ℚ) / (2 * (n : ℚ) + 1) +
        (∑ k ∈ Finset.range n, (1 : ℚ) / ((2 * ((k : ℚ) + 1)) ^ 3 - 2 * ((k : ℚ) + 1))) := by
  clear hn
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ram_shift, ih, Finset.sum_range_succ]
    have h1 : (2 * (n : ℚ) + 1) ≠ 0 := by positivity
    have h2 : (2 * (n : ℚ) + 2) ≠ 0 := by positivity
    have h3 : (2 * ((n : ℚ) + 1) + 1) ≠ 0 := by positivity
    have h4 : (2 * ((n : ℚ) + 1)) ^ 3 - 2 * ((n : ℚ) + 1)
        = 2 * ((n : ℚ) + 1) * (2 * (n : ℚ) + 1) * (2 * (n : ℚ) + 3) := by ring
    have h5 : (2 * (n : ℚ) + 3) ≠ 0 := by positivity
    have h6 : (n : ℚ) + 1 ≠ 0 := by positivity
    push_cast
    rw [h4]
    field_simp
    ring
