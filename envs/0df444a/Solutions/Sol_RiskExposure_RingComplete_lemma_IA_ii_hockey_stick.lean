-- Prove2me | solution 1 for RiskExposure.RingComplete.lemma_IA_ii_hockey_stick
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T10:22:03.185812+00:00
-- url     : https://prove2.me/submissions/06f8c73f-db3a-4a76-b98c-640deeff3f87

import Mathlib
set_option autoImplicit false

theorem solution (n r : ℕ) (h : r < n) :
    ∑ l ∈ Finset.Icc r n, (l.choose r : ℝ) * ((n : ℝ) - l) =
      ((n + 1).choose (r + 1) : ℝ) * (((n : ℝ) - r) / ((r : ℝ) + 2)) := by
  have h' : r ≤ n := h.le
  clear h
  induction n, h' using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hs : ∑ l ∈ Finset.Icc r (n + 1), (l.choose r : ℝ) * (((n + 1 : ℕ) : ℝ) - l)
        = ∑ l ∈ Finset.Icc r n, (l.choose r : ℝ) * (((n + 1 : ℕ) : ℝ) - l) := by
      rw [Finset.sum_Icc_succ_top (by omega : r ≤ n + 1)]
      simp
    have hsum : ∑ l ∈ Finset.Icc r n, (l.choose r : ℝ) = ((n + 1).choose (r + 1) : ℝ) := by
      exact_mod_cast Nat.sum_Icc_choose n r
    have h2 : ∑ l ∈ Finset.Icc r n, (l.choose r : ℝ) * (((n + 1 : ℕ) : ℝ) - l)
        = ∑ l ∈ Finset.Icc r n, (l.choose r : ℝ) * ((n : ℝ) - l)
          + ∑ l ∈ Finset.Icc r n, (l.choose r : ℝ) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      push_cast; ring
    rw [hs, h2, ih, hsum]
    have key := Nat.choose_mul_succ_eq (n + 1) (r + 1)
    have key' : ((n + 1).choose (r + 1) : ℝ) * ((n : ℝ) + 2)
        = ((n + 2).choose (r + 1) : ℝ) * ((n : ℝ) + 1 - r) := by
      have := congrArg (fun x : ℕ => (x : ℝ)) key
      simp only [Nat.cast_mul] at this
      have e : ((n + 1 + 1 - (r + 1) : ℕ) : ℝ) = (n : ℝ) + 1 - r := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [e] at this
      push_cast at this ⊢
      linarith
    have hr : ((r : ℝ) + 2) ≠ 0 := by positivity
    push_cast
    field_simp
    have : ((n + 1 + 1).choose (r + 1) : ℝ) = ((n + 2).choose (r + 1) : ℝ) := rfl
    rw [this]
    linear_combination (↑(r:ℕ) + 2 : ℝ) * 0 + key'
