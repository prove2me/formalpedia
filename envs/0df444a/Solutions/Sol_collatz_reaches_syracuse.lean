-- Prove2me | solution 1 for collatz_reaches_syracuse
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T04:29:38.170826+00:00
-- url     : https://prove2.me/submissions/e3ef36a6-980c-4196-91e7-a082925a6b30

import Mathlib
import Definitions.Def_collatzStepMap
import Definitions.Def_syracuseStep
import Theorems.Thm_collatz_iterate_halving

theorem solution (n : ℕ) (hn : ¬ Even n) :
    ∃ M : ℕ, 0 < M ∧ collatzStep^[M] n = syracuseStep n := by
  set v := (3 * n + 1).factorization 2 with hv
  refine ⟨v + 1, Nat.succ_pos _, ?_⟩
  have hstep : collatzStep n = 3 * n + 1 := by simp [collatzStep, hn]
  have hsplit : 2 ^ v * syracuseStep n = 3 * n + 1 :=
    Nat.ordProj_mul_ordCompl_eq_self (3 * n + 1) 2
  have hdvd : 2 ^ v ∣ 3 * n + 1 := ⟨syracuseStep n, hsplit.symm⟩
  rw [Function.iterate_succ_apply, hstep, collatz_iterate_halving v (3 * n + 1) hdvd,
    ← hsplit, Nat.mul_div_cancel_left]
  positivity
