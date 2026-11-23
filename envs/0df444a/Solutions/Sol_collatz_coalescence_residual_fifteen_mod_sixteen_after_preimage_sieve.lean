-- Prove2me | solution 1 for collatz_coalescence_residual_fifteen_mod_sixteen_after_preimage_sieve
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Siyuan Chen
-- created : 2026-11-23T15:53:02.13994+00:00
-- url     : https://prove2.me/submissions/4330cdd3-3860-44f8-aac9-a14a1099f746
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_collatzStepMap
import Definitions.Def_collatzMinPreimage
import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Theorems.Thm_collatz_iterate_pos
import Theorems.Thm_collatz_reaches_syracuse_iterate
import Theorems.Thm_syracuse_descent_fifteen_mod_sixteen

/-- Residual orbit mergers in the fifteen-mod-16 branch, discharged by the Syracuse descent of
the branch: the accelerated drop `T^t(n) < n` is a positive point of the classical Collatz orbit
of `n` (`collatz_reaches_syracuse_iterate`, `collatz_iterate_pos`), so it is a positive smaller
starting value whose orbit meets the orbit of `n` at itself. -/
theorem solution (n : ℕ)
    (hlarge : 2310000 ≤ n) (hclass : n % 16 = 15)
    (hmod9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7)
    (hpreimage : ∀ t : ℕ, t ≤ 128 → n ≤ collatzMinPreimage 16 (collatzStep^[t] n))
    (h81 : n % 81 ≠ 10)
    (h2304 : n % 2304 ≠ 1743 ∧ n % 2304 ≠ 1599)
    (h4608 : n % 4608 ≠ 2847 ∧ n % 4608 ≠ 735 ∧ n % 4608 ≠ 991 ∧
      n % 4608 ≠ 2527 ∧ n % 4608 ≠ 3039 ∧ n % 4608 ≠ 4575) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  have hn0 : 0 < n := by omega
  have hnodd : ¬ Even n := Nat.not_even_iff.mpr (by omega)
  obtain ⟨t, ht⟩ := syracuse_descent_fifteen_mod_sixteen n hclass
  obtain ⟨M, hM⟩ := collatz_reaches_syracuse_iterate n hnodd t
  refine ⟨syracuseStep^[t] n, M, 0, ?_, ht, ?_⟩
  · rw [← hM]
    exact collatz_iterate_pos M n hn0
  · simp only [Function.iterate_zero, id_eq]
    exact hM
