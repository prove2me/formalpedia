-- Prove2me | solution 1 for SuttonBartoRL.NStep.nStepReturn_recursive
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T11:53:11.325886+00:00
-- url     : https://prove2.me/submissions/198b7988-5150-4558-8cc8-7396da60b4b0

import Mathlib
import Definitions.Def_SuttonBartoRL_NStep_EpisodeReturns

open SuttonBartoRL.NStep in
theorem solution {S : Type} (γ : ℝ) (R : ℕ → ℝ) (St : ℕ → S) (T : ℕ)
    (V : S → ℝ) (t h : ℕ) (hth : t < h) (hhT : h < T) :
    nStepReturn γ R St T V h h = V (St h) ∧
      nStepReturn γ R St T V t h = R (t + 1) + γ * nStepReturn γ R St T V (t + 1) h := by
  constructor
  · simp [nStepReturn, hhT]
  · obtain ⟨m, rfl⟩ : ∃ m, h = t + 1 + m := ⟨h - (t + 1), by omega⟩
    simp only [nStepReturn, hhT, if_true]
    have e1 : t + 1 + m - t = m + 1 := by omega
    have e2 : t + 1 + m - (t + 1) = m := by omega
    rw [e1, e2, Finset.sum_range_succ', mul_add, Finset.mul_sum]
    have hk : ∀ k ∈ Finset.range m, γ ^ (k + 1) * R (t + (k + 1) + 1)
        = γ * (γ ^ k * R (t + 1 + k + 1)) := by
      intro k _
      rw [show t + (k + 1) + 1 = t + 1 + k + 1 by omega]
      ring
    rw [Finset.sum_congr rfl hk]
    simp only [pow_zero, one_mul, add_zero, pow_succ]
    ring
