-- Prove2me | solution 1 for collatz_iterate_halving
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T04:29:37.328765+00:00
-- url     : https://prove2.me/submissions/5d93e18a-9523-407f-9ce9-96084d5e5ef5

import Mathlib
import Definitions.Def_collatzStepMap

theorem solution (k x : ℕ) (h : 2 ^ k ∣ x) : collatzStep^[k] x = x / 2 ^ k := by
  have key : ∀ j c : ℕ, collatzStep^[j] (2 ^ j * c) = c := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        intro c
        have hev : Even (2 ^ (j + 1) * c) := ⟨2 ^ j * c, by ring⟩
        have hstep : collatzStep (2 ^ (j + 1) * c) = 2 ^ j * c := by
          have h1 : collatzStep (2 ^ (j + 1) * c) = 2 ^ (j + 1) * c / 2 := by
            simp [collatzStep, hev]
          have h2 : (2 : ℕ) ^ (j + 1) * c = 2 ^ j * c * 2 := by ring
          rw [h1, h2, Nat.mul_div_cancel _ (by norm_num)]
        rw [Function.iterate_succ_apply, hstep, ih]
  obtain ⟨c, hc⟩ := h
  subst hc
  rw [key, Nat.mul_div_cancel_left]
  positivity
