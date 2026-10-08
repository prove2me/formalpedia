-- Prove2me | solution 1 for SuttonBartoRL.NStep.nStepError_eq_sum_tdError
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T11:16:11.489402+00:00
-- url     : https://prove2.me/submissions/587aa351-86c1-415f-83b4-15e0a5d51bef

import Mathlib
import Definitions.Def_SuttonBartoRL_NStep_EpisodeReturns

open SuttonBartoRL.NStep in
lemma a0f03d8a_telescope {S : Type} (γ : ℝ) (R : ℕ → ℝ) (St : ℕ → S) (V : S → ℝ) (t : ℕ) :
    ∀ j : ℕ, ∑ i ∈ Finset.range j, γ ^ i * tdError γ R St V (t + i) =
      ∑ i ∈ Finset.range j, γ ^ i * R (t + i + 1) + γ ^ j * V (St (t + j)) - V (St t) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    unfold tdError
    rw [show t + j + 1 = t + (j + 1) by omega, pow_succ]
    ring

open SuttonBartoRL.NStep in
theorem solution {S : Type} (γ : ℝ) (R : ℕ → ℝ) (St : ℕ → S) (T : ℕ)
    (V : S → ℝ) (hterm : V (St T) = 0) (t n : ℕ) (hn : 1 ≤ n) (ht : t < T) :
    nStepReturn γ R St T V t (t + n) - V (St t) =
      ∑ k ∈ Finset.Ico t (min (t + n) T), γ ^ (k - t) * tdError γ R St V k := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  rw [a0f03d8a_telescope γ R St V t]
  unfold nStepReturn
  split_ifs with h
  · rw [min_eq_left h.le, Nat.add_sub_cancel_left]
  · unfold fullReturn
    rw [min_eq_right (by omega), show t + (T - t) = T by omega, hterm]
    ring
