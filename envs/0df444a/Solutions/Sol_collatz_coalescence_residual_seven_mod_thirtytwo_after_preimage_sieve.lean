-- Prove2me | solution 1 for collatz_coalescence_residual_seven_mod_thirtytwo_after_preimage_sieve
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Siyuan Chen
-- created : 2026-11-23T15:52:52.813672+00:00
-- url     : https://prove2.me/submissions/e6240163-bad3-485d-82f5-09de85a679b0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_collatzStepMap
import Definitions.Def_collatzMinPreimage
import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Theorems.Thm_collatz_iterate_pos
import Theorems.Thm_collatz_reaches_syracuse_iterate
import Theorems.Thm_syracuse_descent_seven_mod_thirtytwo

/-- Residual orbit mergers in the seven-mod-32 branch, discharged by the Syracuse descent of
the branch: the accelerated drop `T^t(n) < n` is a point of the classical Collatz orbit of `n`
(`collatz_reaches_syracuse_iterate`), and it is positive (`collatz_iterate_pos`). It is therefore a
positive smaller starting value whose orbit meets the orbit of `n` at itself. -/
theorem solution (n : ℕ)
    (hlarge : 2310000 ≤ n) (hclass : n % 32 = 7)
    (hmod9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7)
    (hpreimage : ∀ t : ℕ, t ≤ 128 → n ≤ collatzMinPreimage 16 (collatzStep^[t] n))
    (h81 : n % 81 ≠ 10)
    (h4608 : n % 4608 ≠ 4071)
    (h9216 : n % 9216 ≠ 7783) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  have hn0 : 0 < n := by omega
  have hnodd : ¬ Even n := Nat.not_even_iff.mpr (by omega)
  obtain ⟨t, ht⟩ := syracuse_descent_seven_mod_thirtytwo n hclass
  obtain ⟨M, hM⟩ := collatz_reaches_syracuse_iterate n hnodd t
  refine ⟨syracuseStep^[t] n, M, 0, ?_, ht, ?_⟩
  · rw [← hM]
    exact collatz_iterate_pos M n hn0
  · simp only [Function.iterate_zero, id_eq]
    exact hM
