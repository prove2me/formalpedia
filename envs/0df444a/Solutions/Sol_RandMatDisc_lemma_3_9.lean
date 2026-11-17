-- Prove2me | solution 1 for RandMatDisc.lemma_3_9
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-16T16:05:42.572938+00:00
-- url     : https://prove2.me/submissions/bd0eca85-9968-4820-9d9f-d94d4cf62403

import Mathlib

theorem solution :
    ∀ C : ℝ, 0 < C → ∃ A : ℝ, 1 ≤ A ∧ ∀ y : ℕ → ℝ, (∀ k, 0 ≤ y k) →
      (∀ k, y (k + 1) ≤ C * (Real.sqrt (y k) + 1)) →
      (∀ k : ℕ, ⌈Real.logb 2 (max (y 0) 1)⌉₊ ≤ k → y k ≤ A) ∧
      (∀ k, y k ≤ max (y 0) A) := by
  intro C hC
  refine ⟨(2 * C + 2) ^ 2, by nlinarith [hC], ?_⟩
  intro y hy0 hrec
  have hstep : ∀ k, y k ≤ (2 * C + 2) ^ 2 → y (k + 1) ≤ (2 * C + 2) ^ 2 := by
    intro k hk
    have h1 : Real.sqrt (y k) ≤ 2 * C + 2 := by
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * C + 2)]
      exact Real.sqrt_le_sqrt hk
    calc y (k + 1) ≤ C * (Real.sqrt (y k) + 1) := hrec k
      _ ≤ C * ((2 * C + 2) + 1) := by nlinarith [h1, hC]
      _ ≤ (2 * C + 2) ^ 2 := by nlinarith [hC]
  have hbig : ∀ k, (2 * C + 2) ^ 2 < y k → y (k + 1) ≤ y k / 2 := by
    intro k hk
    have ht : 2 * C + 2 < Real.sqrt (y k) := by
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * C + 2)]
      exact Real.sqrt_lt_sqrt (by positivity) hk
    have hyk : y k = Real.sqrt (y k) ^ 2 := (Real.sq_sqrt (hy0 k)).symm
    calc y (k + 1) ≤ C * (Real.sqrt (y k) + 1) := hrec k
      _ ≤ y k / 2 := by nlinarith [ht, hC, hyk]
  constructor
  · intro k hk
    by_contra hcon
    simp only [not_le] at hcon
    have hinv : ∀ j, (2 * C + 2) ^ 2 < y j → y j ≤ y 0 / 2 ^ j := by
      intro j
      induction j with
      | zero => intro _; simp
      | succ j ih =>
        intro hj
        have hyj : (2 * C + 2) ^ 2 < y j := by
          by_contra h
          simp only [not_lt] at h
          have := hstep j h
          linarith
        have h1 := ih hyj
        have h2 := hbig j hyj
        have h3 : y 0 / 2 ^ j / 2 = y 0 / 2 ^ (j + 1) := by
          rw [pow_succ]
          ring
        calc y (j + 1) ≤ y j / 2 := h2
          _ ≤ y 0 / 2 ^ j / 2 := by nlinarith [h1]
          _ = y 0 / 2 ^ (j + 1) := h3
    have h2pow : y 0 ≤ 2 ^ k := by
      have hk' : Real.logb 2 (max (y 0) 1) ≤ (k : ℝ) := Nat.ceil_le.mp hk
      have hMpos : 0 < max (y 0) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
      have h4 := (Real.logb_le_iff_le_rpow (by norm_num) hMpos).mp hk'
      rw [Real.rpow_natCast] at h4
      exact le_trans (le_max_left _ _) h4
    have h5 := hinv k hcon
    have h6 : y 0 / 2 ^ k ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact h2pow
    have h7 : (1 : ℝ) ≤ (2 * C + 2) ^ 2 := by nlinarith [hC]
    linarith
  · intro k
    induction k with
    | zero => exact le_max_left _ _
    | succ k ih =>
      by_cases h : y k ≤ (2 * C + 2) ^ 2
      · exact le_trans (hstep k h) (le_max_right _ _)
      · simp only [not_le] at h
        have h1 := hbig k h
        have h2 : 0 ≤ y k := hy0 k
        have h3 : y k / 2 ≤ y k := by linarith
        exact le_trans (le_trans h1 h3) ih
