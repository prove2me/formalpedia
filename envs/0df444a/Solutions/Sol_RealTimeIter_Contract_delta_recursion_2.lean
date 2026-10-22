-- Prove2me | solution 2 for RealTimeIter.Contract.delta_recursion
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:31:53.508177+00:00
-- url     : https://prove2.me/submissions/f7a95f84-e6a4-4a5d-8507-ee90d9217eb7

import Mathlib
set_option autoImplicit false

theorem solution (κ ω : ℝ) (hω : 0 ≤ ω) (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    (hδ0 : κ + ω / 2 * a 0 < 1)
    (hrec : ∀ k, a (k + 1) ≤ (κ + ω / 2 * a k) * a k) :
    ∀ k, κ + ω / 2 * a (k + 1) ≤ κ + ω / 2 * a k ∧
      κ + ω / 2 * a k ≤ κ + ω / 2 * a 0 ∧
      a k ≤ (κ + ω / 2 * a 0) ^ k * a 0 := by
  set δ : ℕ → ℝ := fun k => κ + ω / 2 * a k with hδ
  -- δ k < 1 and δ monotone, by induction
  have main : ∀ k, δ k ≤ δ 0 ∧ δ (k + 1) ≤ δ k := by
    -- first, δ k < 1 → δ (k+1) ≤ δ k
    have step : ∀ k, δ k < 1 → δ (k + 1) ≤ δ k := by
      intro k hk
      have h1 := hrec k
      have : a (k + 1) ≤ a k := by
        have : (κ + ω / 2 * a k) * a k ≤ 1 * a k := mul_le_mul_of_nonneg_right hk.le (ha k)
        linarith
      simp only [hδ]
      nlinarith [hω]
    have lt1 : ∀ k, δ k ≤ δ 0 := by
      intro k
      induction k with
      | zero => exact le_refl _
      | succ n ih =>
        have : δ n < 1 := lt_of_le_of_lt ih hδ0
        exact le_trans (step n this) ih
    intro k
    exact ⟨lt1 k, step k (lt_of_le_of_lt (lt1 k) hδ0)⟩
  intro k
  refine ⟨(main k).2, (main k).1, ?_⟩
  by_cases h0 : a 0 = 0
  · have hz : ∀ n, a n = 0 := by
      intro n
      induction n with
      | zero => exact h0
      | succ m ih =>
        have h1 := hrec m
        rw [ih] at h1
        simp at h1
        exact le_antisymm h1 (ha _)
    rw [hz k, h0]; simp
  · have hpos : 0 < a 0 := lt_of_le_of_ne (ha 0) (Ne.symm h0)
    have hδnn : 0 ≤ δ 0 := by
      have h1 := hrec 0
      have h2 : 0 ≤ δ 0 * a 0 := le_trans (ha 1) h1
      by_contra hneg
      push_neg at hneg
      nlinarith
    induction k with
    | zero => simp
    | succ n ih =>
      have h1 := hrec n
      have hle : δ n ≤ δ 0 := (main n).1
      have hnn : 0 ≤ a n := ha n
      have ih' := ih
      calc a (n + 1) ≤ δ n * a n := h1
        _ ≤ δ 0 * a n := mul_le_mul_of_nonneg_right hle hnn
        _ ≤ δ 0 * (δ 0 ^ n * a 0) := mul_le_mul_of_nonneg_left ih' hδnn
        _ = δ 0 ^ (n + 1) * a 0 := by ring
