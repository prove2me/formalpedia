-- Prove2me | solution 1 for OrderedExperts.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T12:36:01.70501+00:00
-- url     : https://prove2.me/submissions/273bcf1d-251a-4f59-a51e-626fa8e25038

import Mathlib

open Finset

theorem solution :
    (∀ (s : ℕ → ℝ) (b : ℕ), 1 ≤ b → 0 ≤ s (b - 1) → (∀ j, b ≤ j → s (j - 1) < s j) →
      ∀ N : ℕ, ∑ j ∈ Icc b N, (s j - s (j - 1)) / s j ^ 2 ≤ 2 / s b) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℕ → ℝ) (b : ℕ), 1 ≤ b → 0 ≤ s (b - 1) →
      (∀ j, b ≤ j → s (j - 1) < s j) → ∀ α : ℝ, 0 < α → ∀ N : ℕ,
        ∑ j ∈ Icc b N, (s j - s (j - 1)) / (s j ^ 2 * (α + s j) ^ 2) ≤
          C / (s b * (α + s b) ^ 2) := by
  have key : ∀ (s : ℕ → ℝ) (b : ℕ), 1 ≤ b → 0 ≤ s (b - 1) →
      (∀ j, b ≤ j → s (j - 1) < s j) →
      (∀ N : ℕ, ∑ j ∈ Icc b N, (s j - s (j - 1)) / s j ^ 2 ≤ 2 / s b) ∧
      (∀ (α : ℝ), 0 < α → ∀ N : ℕ,
        ∑ j ∈ Icc b N, (s j - s (j - 1)) / (s j ^ 2 * (α + s j) ^ 2) ≤
          2 / (s b * (α + s b) ^ 2)) := by
    intro s b hb h0 hmono
    have hsb : 0 < s b := lt_of_le_of_lt h0 (hmono b le_rfl)
    have hsbne : s b ≠ 0 := hsb.ne'
    have hge : ∀ j, b ≤ j → s b ≤ s j := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => exact le_rfl
      | succ k hk ih =>
          have hstep : s k ≤ s (k + 1) := by
            have h := hmono (k + 1) (by omega)
            simpa using h.le
          exact ih.trans hstep
    have hpos : ∀ j, b ≤ j → 0 < s j := fun j hj => lt_of_lt_of_le hsb (hge j hj)
    -- telescoping identity for `1 / s`
    have tel : ∀ N, b ≤ N →
        ∑ j ∈ Icc (b + 1) N, (1 / s (j - 1) - 1 / s j) = 1 / s b - 1 / s N := by
      intro N hN
      induction N, hN using Nat.le_induction with
      | base => simp
      | succ k hk ih =>
          rw [Finset.sum_Icc_succ_top (a := b + 1) (b := k) (by omega), ih]
          simp only [Nat.add_sub_cancel]
          have hsk : s k ≠ 0 := (hpos k hk).ne'
          have hsk1 : s (k + 1) ≠ 0 := (hpos (k + 1) (by omega)).ne'
          field_simp [hsbne, hsk, hsk1]
          ring
    -- pointwise telescoping kernel
    have key1 : ∀ j, b + 1 ≤ j →
        (s j - s (j - 1)) / s j ^ 2 ≤ 1 / s (j - 1) - 1 / s j := by
      intro j hj
      have hj1 : b ≤ j - 1 := by omega
      have hx : 0 < s (j - 1) := hpos (j - 1) hj1
      have hy : 0 < s j := hpos j (by omega)
      have hxy : s (j - 1) ≤ s j := (hmono j (by omega)).le
      have hmul : s (j - 1) * s j ≤ s j * s j := mul_le_mul_of_nonneg_right hxy hy.le
      rw [div_le_iff₀ (pow_pos hy 2)]
      field_simp [hx.ne', hy.ne']
      nlinarith [hmul]
    constructor
    · -- first clause
      intro N
      rcases lt_or_ge N b with hN | hN
      · rw [Icc_eq_empty_of_lt hN]
        simp only [sum_empty]
        exact div_nonneg (by norm_num) hsb.le
      · have hsplit : Icc b N = insert b (Icc (b + 1) N) := by
          ext x
          simp only [mem_Icc, mem_insert]
          omega
        rw [hsplit, sum_insert (by simp)]
        have hfirst : (s b - s (b - 1)) / s b ^ 2 ≤ 1 / s b := by
          rw [div_le_iff₀ (pow_pos hsb 2)]
          have hone : (1 / s b) * s b ^ 2 = s b := by
            field_simp
          rw [hone]
          linarith
        have htail : ∑ j ∈ Icc (b + 1) N, (s j - s (j - 1)) / s j ^ 2
            ≤ 1 / s b - 1 / s N := by
          calc ∑ j ∈ Icc (b + 1) N, (s j - s (j - 1)) / s j ^ 2
              ≤ ∑ j ∈ Icc (b + 1) N, (1 / s (j - 1) - 1 / s j) := by
                apply sum_le_sum
                intro j hj
                exact key1 j (mem_Icc.mp hj).1
            _ = 1 / s b - 1 / s N := tel N hN
        have htail2 : 1 / s b - 1 / s N ≤ 1 / s b := by
          have : 0 ≤ 1 / s N := div_nonneg zero_le_one (hpos N hN).le
          linarith
        have h2 : (2 : ℝ) / s b = 1 / s b + 1 / s b := by ring
        calc (s b - s (b - 1)) / s b ^ 2
              + ∑ j ∈ Icc (b + 1) N, (s j - s (j - 1)) / s j ^ 2
            ≤ 1 / s b + (1 / s b - 1 / s N) := add_le_add hfirst htail
          _ ≤ 2 / s b := by rw [h2]; linarith [htail2]
    · -- second clause, with the explicit constant C = 2
      intro α hα N
      rcases lt_or_ge N b with hN | hN
      · rw [Icc_eq_empty_of_lt hN]
        simp only [sum_empty]
        exact div_nonneg (by norm_num) (mul_nonneg hsb.le (sq_nonneg _))
      · have hsplit : Icc b N = insert b (Icc (b + 1) N) := by
          ext x
          simp only [mem_Icc, mem_insert]
          omega
        rw [hsplit, sum_insert (by simp)]
        have hαb : 0 < α + s b := by linarith
        have key2 : ∀ j, b + 1 ≤ j →
            (s j - s (j - 1)) / (s j ^ 2 * (α + s j) ^ 2) ≤
              (1 / s (j - 1) - 1 / s j) / (α + s b) ^ 2 := by
          intro j hj
          have hj1 : b ≤ j - 1 := by omega
          have hx : 0 < s (j - 1) := hpos (j - 1) hj1
          have hy : 0 < s j := hpos j (by omega)
          have hle : α + s b ≤ α + s j := by
            have := hge j (by omega); linarith
          have h1 := key1 j hj
          have h2 : 1 / (α + s j) ^ 2 ≤ 1 / (α + s b) ^ 2 := by
            apply one_div_le_one_div_of_le (pow_pos hαb 2)
            exact pow_le_pow_left₀ hαb.le hle 2
          have hnn : 0 ≤ 1 / s (j - 1) - 1 / s j := by
            have hlt : s (j - 1) < s j := hmono j (by omega)
            have hle' : 1 / s j ≤ 1 / s (j - 1) := one_div_le_one_div_of_le hx hlt.le
            linarith
          calc (s j - s (j - 1)) / (s j ^ 2 * (α + s j) ^ 2)
              = ((s j - s (j - 1)) / s j ^ 2) * (1 / (α + s j) ^ 2) := by
                rw [div_mul_div_comm, mul_one]
            _ ≤ (1 / s (j - 1) - 1 / s j) * (1 / (α + s j) ^ 2) :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ ≤ (1 / s (j - 1) - 1 / s j) * (1 / (α + s b) ^ 2) :=
                mul_le_mul_of_nonneg_left h2 hnn
            _ = (1 / s (j - 1) - 1 / s j) / (α + s b) ^ 2 := by
                rw [mul_one_div]
        have htail : ∑ j ∈ Icc (b + 1) N,
              (s j - s (j - 1)) / (s j ^ 2 * (α + s j) ^ 2)
            ≤ (1 / s b - 1 / s N) / (α + s b) ^ 2 := by
          calc ∑ j ∈ Icc (b + 1) N, (s j - s (j - 1)) / (s j ^ 2 * (α + s j) ^ 2)
              ≤ ∑ j ∈ Icc (b + 1) N,
                  (1 / s (j - 1) - 1 / s j) / (α + s b) ^ 2 := by
                apply sum_le_sum
                intro j hj
                exact key2 j (mem_Icc.mp hj).1
            _ = (∑ j ∈ Icc (b + 1) N, (1 / s (j - 1) - 1 / s j)) / (α + s b) ^ 2 := by
                rw [sum_div]
            _ = (1 / s b - 1 / s N) / (α + s b) ^ 2 := by rw [tel N hN]
        have htail2 : (1 / s b - 1 / s N) / (α + s b) ^ 2
            ≤ 1 / (s b * (α + s b) ^ 2) := by
          have h1 : 1 / s b - 1 / s N ≤ 1 / s b := by
            have : 0 ≤ 1 / s N := div_nonneg zero_le_one (hpos N hN).le
            linarith
          have h2 : (1 / s b - 1 / s N) / (α + s b) ^ 2 ≤ (1 / s b) / (α + s b) ^ 2 :=
            div_le_div_of_nonneg_right h1 (sq_nonneg _)
          have heq : (1 / s b) / (α + s b) ^ 2 = 1 / (s b * (α + s b) ^ 2) := by
            rw [div_div]
          linarith [h2, heq.le, heq.ge]
        have hfirst : (s b - s (b - 1)) / (s b ^ 2 * (α + s b) ^ 2)
            ≤ 1 / (s b * (α + s b) ^ 2) := by
          rw [div_le_iff₀ (mul_pos (pow_pos hsb 2) (pow_pos hαb 2))]
          have hone : (1 / (s b * (α + s b) ^ 2)) * (s b ^ 2 * (α + s b) ^ 2) = s b := by
            field_simp [hsbne, hαb.ne']
          rw [hone]
          linarith
        have h2 : (2 : ℝ) / (s b * (α + s b) ^ 2)
            = 1 / (s b * (α + s b) ^ 2) + 1 / (s b * (α + s b) ^ 2) := by ring
        calc (s b - s (b - 1)) / (s b ^ 2 * (α + s b) ^ 2)
              + ∑ j ∈ Icc (b + 1) N, (s j - s (j - 1)) / (s j ^ 2 * (α + s j) ^ 2)
            ≤ 1 / (s b * (α + s b) ^ 2) + (1 / s b - 1 / s N) / (α + s b) ^ 2 :=
              add_le_add hfirst htail
          _ ≤ 2 / (s b * (α + s b) ^ 2) := by rw [h2]; linarith [htail2]
  constructor
  · intro s b hb h0 hmono N
    exact (key s b hb h0 hmono).1 N
  · refine ⟨2, by norm_num, ?_⟩
    intro s b hb h0 hmono α hα N
    exact (key s b hb h0 hmono).2 α hα N
