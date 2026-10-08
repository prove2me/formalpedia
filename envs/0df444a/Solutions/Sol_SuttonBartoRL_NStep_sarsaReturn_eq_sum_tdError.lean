-- Prove2me | solution 1 for SuttonBartoRL.NStep.sarsaReturn_eq_sum_tdError
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:44:16.283035+00:00
-- url     : https://prove2.me/submissions/3997e78c-4498-4091-8622-ae96c9f6a22e

import Mathlib
import Definitions.Def_SuttonBartoRL_NStep_EpisodeReturns

set_option autoImplicit false

open SuttonBartoRL.NStep in
theorem a971c3b7_tele {S A : Type} (γ : ℝ) (R : ℕ → ℝ) (St : ℕ → S)
    (At : ℕ → A) (Q : ℤ → S → A → ℝ) (t : ℕ) (m : ℕ) :
    ∑ j ∈ Finset.range m, γ ^ j * sarsaTDError γ R St At Q (t + j) =
      ∑ j ∈ Finset.range m, γ ^ j * R (t + j + 1) +
        γ ^ m * Q (((t + m : ℕ) : ℤ) - 1) (St (t + m)) (At (t + m)) -
        Q ((t : ℤ) - 1) (St t) (At t) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    unfold sarsaTDError
    have h1 : (((t + (m + 1) : ℕ) : ℤ) - 1) = ((t + m : ℕ) : ℤ) := by push_cast; ring
    rw [h1, show t + (m + 1) = t + m + 1 by ring, pow_succ]
    ring

open SuttonBartoRL.NStep in
theorem solution {S A : Type} (γ : ℝ) (R : ℕ → ℝ) (St : ℕ → S)
    (At : ℕ → A) (T : ℕ) (Q : ℤ → S → A → ℝ) (hterm : ∀ (k : ℤ) (a : A), Q k (St T) a = 0)
    (t n : ℕ) (hn : 1 ≤ n) (ht : t < T) :
    sarsaReturn γ R St At T Q t n =
      Q ((t : ℤ) - 1) (St t) (At t) +
        ∑ k ∈ Finset.Ico t (min (t + n) T), γ ^ (k - t) * sarsaTDError γ R St At Q k := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hle : t ≤ min (t + n) T := le_min (Nat.le_add_right t n) ht.le
  simp only [Nat.add_sub_cancel_left]
  rw [a971c3b7_tele]
  unfold sarsaReturn
  split_ifs with h
  · have hm : min (t + n) T = t + n := min_eq_left h.le
    rw [hm, Nat.add_sub_cancel_left]
    have h2 : (((t + n : ℕ) : ℤ) - 1) = (t : ℤ) + n - 1 := by push_cast; ring
    rw [h2]
    ring
  · have hm : min (t + n) T = T := min_eq_right (by omega)
    rw [hm, Nat.add_sub_cancel' ht.le, hterm]
    unfold fullReturn
    ring
