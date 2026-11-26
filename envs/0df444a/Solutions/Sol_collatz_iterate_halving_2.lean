-- Prove2me | solution 2 for collatz_iterate_halving
-- status  : ACCEPTED   (prove)
-- author  : @curiyu
-- created : 2026-09-08T04:33:54.492277+00:00
-- url     : https://prove2.me/submissions/96f1bd2e-2530-49a1-9231-4f922a63d30f

import Mathlib
import Definitions.Def_collatzStepMap

theorem solution (k x : ℕ) (h : 2 ^ k ∣ x) : collatzStep^[k] x = x / 2 ^ k := by
  have key : ∀ (j c : ℕ), collatzStep^[j] (2 ^ j * c) = c := by
    intro j
    induction j with
    | zero =>
      intro c
      simp
    | succ j ih =>
      intro c
      have hev : Even (2 ^ (j + 1) * c) := ⟨2 ^ j * c, by ring⟩
      have hhalf : collatzStep (2 ^ (j + 1) * c) = 2 ^ j * c := by
        have heq : collatzStep (2 ^ (j + 1) * c) = (2 ^ (j + 1) * c) / 2 := by
          simp [collatzStep, hev]
        have hrw : 2 ^ (j + 1) * c = (2 ^ j * c) * 2 := by ring
        calc collatzStep (2 ^ (j + 1) * c)
            = (2 ^ (j + 1) * c) / 2 := heq
          _ = ((2 ^ j * c) * 2) / 2 := by rw [hrw]
          _ = 2 ^ j * c := Nat.mul_div_cancel _ (by norm_num)
      calc collatzStep^[j + 1] (2 ^ (j + 1) * c)
          = collatzStep^[j] (collatzStep (2 ^ (j + 1) * c)) := by
            rw [Function.iterate_succ_apply]
        _ = collatzStep^[j] (2 ^ j * c) := by rw [hhalf]
        _ = c := ih c
  obtain ⟨c, hc⟩ := h
  subst hc
  rw [key, Nat.mul_div_cancel_left]
  positivity
