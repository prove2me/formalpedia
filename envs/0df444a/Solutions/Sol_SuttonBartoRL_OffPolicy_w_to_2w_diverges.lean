-- Prove2me | solution 1 for SuttonBartoRL.OffPolicy.w_to_2w_diverges
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T11:14:10.666136+00:00
-- url     : https://prove2.me/submissions/4c7bfbc6-b709-4080-a858-1882ed5f94db

import Mathlib

open Filter

open Filter in
theorem solution (α γ : ℝ) (hα : 0 < α) (hγ : 1 / 2 < γ) (hγ1 : γ ≤ 1)
    (w : ℕ → ℝ)
    (hupd : ∀ t, w (t + 1) = w t + α * 1 * (0 + γ * (2 * w t) - 1 * w t) * 1) :
    (∀ t, w (t + 1) = (1 + α * (2 * γ - 1)) * w t) ∧
    1 < 1 + α * (2 * γ - 1) ∧
    (0 < w 0 → Tendsto w atTop atTop) ∧
    (w 0 < 0 → Tendsto w atTop atBot) := by
  have h1 : ∀ t, w (t + 1) = (1 + α * (2 * γ - 1)) * w t := by
    intro t; rw [hupd t]; ring
  have h2 : 1 < 1 + α * (2 * γ - 1) := by
    have : 0 < 2 * γ - 1 := by linarith
    have := mul_pos hα this
    linarith
  have hw : ∀ t, w t = (1 + α * (2 * γ - 1)) ^ t * w 0 := by
    intro t
    induction t with
    | zero => simp
    | succ n ih => rw [h1 n, ih, pow_succ]; ring
  have hT : Tendsto (fun n : ℕ => (1 + α * (2 * γ - 1)) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt h2
  refine ⟨h1, h2, ?_, ?_⟩
  · intro h0
    have : w = fun n => (1 + α * (2 * γ - 1)) ^ n * w 0 := funext hw
    rw [this]
    exact hT.atTop_mul_const h0
  · intro h0
    have : w = fun n => (1 + α * (2 * γ - 1)) ^ n * w 0 := funext hw
    rw [this]
    exact hT.atTop_mul_const_of_neg h0
