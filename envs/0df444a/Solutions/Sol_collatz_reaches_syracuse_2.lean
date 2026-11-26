-- Prove2me | solution 2 for collatz_reaches_syracuse
-- status  : ACCEPTED   (prove)
-- author  : @curiyu
-- created : 2026-09-08T04:34:04.525001+00:00
-- url     : https://prove2.me/submissions/f23411f5-898b-4461-9284-ea3cf1d7b25c

import Mathlib
import Definitions.Def_collatzStepMap
import Definitions.Def_syracuseStep

theorem solution (n : ℕ) (hn : ¬ Even n) :
    ∃ M : ℕ, 0 < M ∧ collatzStep^[M] n = syracuseStep n := by
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
  set v := (3 * n + 1).factorization 2 with hv
  refine ⟨v + 1, Nat.succ_pos _, ?_⟩
  have hstep : collatzStep n = 3 * n + 1 := by simp [collatzStep, hn]
  have hsplit : 2 ^ v * syracuseStep n = 3 * n + 1 :=
    Nat.ordProj_mul_ordCompl_eq_self (3 * n + 1) 2
  have hhalve : collatzStep^[v] (3 * n + 1) = syracuseStep n := by
    conv_lhs => rw [← hsplit]
    exact key v (syracuseStep n)
  calc collatzStep^[v + 1] n
      = collatzStep^[v] (collatzStep n) := by rw [Function.iterate_succ_apply]
    _ = collatzStep^[v] (3 * n + 1) := by rw [hstep]
    _ = syracuseStep n := hhalve
