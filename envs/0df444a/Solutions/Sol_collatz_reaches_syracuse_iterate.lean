-- Prove2me | solution 1 for collatz_reaches_syracuse_iterate
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T04:29:38.531767+00:00
-- url     : https://prove2.me/submissions/453957ad-044c-4b7c-bc14-8979dfc0fdf4

import Mathlib
import Definitions.Def_collatzStepMap
import Definitions.Def_syracuseStep
import Theorems.Thm_collatz_reaches_syracuse
import Theorems.Thm_syracuseStep_odd

theorem solution (n : ℕ) (hn : ¬ Even n) (t : ℕ) :
    ∃ M : ℕ, collatzStep^[M] n = syracuseStep^[t] n := by
  induction t with
  | zero => exact ⟨0, by simp⟩
  | succ t ih =>
      obtain ⟨M, hM⟩ := ih
      have hodd : ¬ Even (syracuseStep^[t] n) := by
        cases t with
        | zero => simpa using hn
        | succ s =>
            rw [Function.iterate_succ_apply']
            simpa [Nat.not_even_iff_odd] using syracuseStep_odd (syracuseStep^[s] n)
      obtain ⟨M', _, hM'⟩ := collatz_reaches_syracuse (syracuseStep^[t] n) hodd
      refine ⟨M' + M, ?_⟩
      rw [Function.iterate_add_apply, hM, hM', Function.iterate_succ_apply']
