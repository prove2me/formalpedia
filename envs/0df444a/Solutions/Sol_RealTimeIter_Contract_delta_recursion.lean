-- Prove2me | solution 1 for RealTimeIter.Contract.delta_recursion
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T16:29:22.015736+00:00
-- url     : https://prove2.me/submissions/99a271af-8ed4-4d87-a129-820d5de5ce2f

import Mathlib

theorem solution (κ ω : ℝ) (hω : 0 ≤ ω) (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    (hδ0 : κ + ω / 2 * a 0 < 1)
    (hrec : ∀ k, a (k + 1) ≤ (κ + ω / 2 * a k) * a k) :
    ∀ k, κ + ω / 2 * a (k + 1) ≤ κ + ω / 2 * a k ∧
      κ + ω / 2 * a k ≤ κ + ω / 2 * a 0 ∧
      a k ≤ (κ + ω / 2 * a 0) ^ k * a 0 := by
  set c := κ + ω / 2 * a 0 with hc
  have hω2 : 0 ≤ ω / 2 := by positivity
  have hle0 : ∀ k, a k ≤ a 0 := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      have hck : κ + ω / 2 * a k ≤ c := by
        have := mul_le_mul_of_nonneg_left ih hω2; linarith
      have := hrec k
      have : (κ + ω / 2 * a k) * a k ≤ a k := by nlinarith [ha k]
      linarith
  have hdec : ∀ k, a (k + 1) ≤ a k := by
    intro k
    have hck : κ + ω / 2 * a k ≤ c := by
      have := mul_le_mul_of_nonneg_left (hle0 k) hω2; linarith
    have := hrec k
    nlinarith [ha k]
  have hpow : ∀ k, a k ≤ c ^ k * a 0 := by
    rcases le_or_gt 0 c with hc0 | hc0
    · intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hck : κ + ω / 2 * a k ≤ c := by
          have := mul_le_mul_of_nonneg_left (hle0 k) hω2; linarith
        calc a (k + 1) ≤ (κ + ω / 2 * a k) * a k := hrec k
          _ ≤ c * a k := mul_le_mul_of_nonneg_right hck (ha k)
          _ ≤ c * (c ^ k * a 0) := mul_le_mul_of_nonneg_left ih hc0
          _ = c ^ (k + 1) * a 0 := by ring
    · have h1 := hrec 0
      have ha0 : a 0 = 0 := by
        have : c * a 0 ≥ 0 := le_trans (ha 1) h1
        nlinarith [ha 0]
      intro k
      rw [ha0, mul_zero]
      have := hle0 k
      linarith
  intro k
  refine ⟨?_, ?_, hpow k⟩
  · have := mul_le_mul_of_nonneg_left (hdec k) hω2; linarith
  · have := mul_le_mul_of_nonneg_left (hle0 k) hω2; linarith
