-- Prove2me | solution 1 for TSPSDPGap.lemma_4_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:49:26.643269+00:00
-- url     : https://prove2.me/submissions/8e3331cb-f0c3-46cb-b580-82c7a651ff59

import Mathlib

namespace Aux_TSP49

theorem shift (m : ℕ) (f : ℕ → ℝ) (hm : 1 ≤ m) :
    ∑ j ∈ Finset.Ico 1 (2 * (m + 1)), (((2 * (m + 1) : ℕ) : ℝ) - j) * f j =
      ∑ j ∈ Finset.Ico 1 (2 * m), (((2 * m : ℕ) : ℝ) - j) * f j +
        2 * ∑ j ∈ Finset.Ico 1 (2 * m), f j + 2 * f (2 * m) + f (2 * m + 1) := by
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_Ico_succ_top (by omega),
    Finset.sum_Ico_succ_top (by omega), Finset.mul_sum, ← Finset.sum_add_distrib]
  have e : ∀ j ∈ Finset.Ico 1 (2 * m), (((2 * m + 1 + 1 : ℕ) : ℝ) - j) * f j =
      (((2 * m : ℕ) : ℝ) - j) * f j + 2 * f j := by
    intro j _; push_cast; ring
  rw [Finset.sum_congr rfl e]
  push_cast
  ring

theorem cnt (m : ℕ) (hm : 1 ≤ m) :
    ∑ j ∈ Finset.Ico 1 (2 * m), (if Odd j then (1 : ℝ) else 0) = m ∧
      ∑ j ∈ Finset.Ico 1 (2 * m), (-1 : ℝ) ^ j = -1 := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [show Finset.Ico 1 (2 * 1) = {1} by rfl]
    constructor <;> simp only [Finset.sum_singleton] <;> norm_num
  | succ m hm ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_Ico_succ_top (by omega),
      Finset.sum_Ico_succ_top (by omega), Finset.sum_Ico_succ_top (by omega),
      Finset.sum_Ico_succ_top (by omega), ih.1, ih.2]
    have h1 : ¬ Odd (2 * m) := by simp
    have h2 : Odd (2 * m + 1) := by simp
    have e1 : (-1 : ℝ) ^ (2 * m) = 1 := by rw [pow_mul]; simp
    have e2 : (-1 : ℝ) ^ (2 * m + 1) = -1 := by rw [pow_succ, e1]; ring
    rw [if_neg h1, if_pos h2, e1, e2]
    push_cast
    constructor <;> ring

end Aux_TSP49

theorem solution (g : ℕ) (hg : Even g) :
    ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * (if Odd j then (1 : ℝ) else 0) = (g : ℝ) ^ 2 / 4 ∧
    ∑ j ∈ Finset.Ico 1 g, ((g : ℝ) - j) * (-1 : ℝ) ^ j = -(g : ℝ) / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, g = 2 * m := by obtain ⟨r, hr⟩ := hg; exact ⟨r, by omega⟩
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0; simp
  have key : ∀ m, 1 ≤ m →
      ∑ j ∈ Finset.Ico (1:ℕ) (2 * m), (((2 * m : ℕ) : ℝ) - (j : ℝ)) *
          (if Odd j then (1 : ℝ) else 0) = (m : ℝ) ^ 2 ∧
      ∑ j ∈ Finset.Ico (1:ℕ) (2 * m), (((2 * m : ℕ) : ℝ) - (j : ℝ)) * (-1 : ℝ) ^ j =
          -(m : ℝ) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      rw [show Finset.Ico 1 (2 * 1) = {1} by rfl]
      norm_num
    | succ m hm ih =>
      rw [Aux_TSP49.shift m _ hm, Aux_TSP49.shift m _ hm, ih.1, ih.2,
        (Aux_TSP49.cnt m hm).1, (Aux_TSP49.cnt m hm).2]
      have h1 : ¬ Odd (2 * m) := by simp
      have h2 : Odd (2 * m + 1) := by simp
      have e1 : (-1 : ℝ) ^ (2 * m) = 1 := by rw [pow_mul]; simp
      have e2 : (-1 : ℝ) ^ (2 * m + 1) = -1 := by rw [pow_succ, e1]; ring
      rw [if_neg h1, if_pos h2, e1, e2]
      push_cast
      constructor <;> ring
  obtain ⟨k1, k2⟩ := key m hpos
  push_cast at k1 k2 ⊢
  constructor
  · rw [k1]; ring
  · rw [k2]; ring
