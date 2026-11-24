-- Prove2me | solution 2 for collatz_coalescence_residual_twentyseven_mod_thirtytwo_after_preimage_sieve
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T07:30:16.78616+00:00
-- url     : https://prove2.me/submissions/2a5533f6-b384-46e2-9a5a-0b97c13a4782
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_collatz_smaller_merger_of_odd_run_divisibility
import Theorems.Thm_collatz_coalescence_residual_twentyseven_mod_thirtytwo_without_odd_run_mergers

theorem solution (n : ℕ)
    (hlarge : 2310000 ≤ n) (hclass : n % 32 = 27)
    (hmod9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7)
    (hpreimage : ∀ t : ℕ, t ≤ 128 → n ≤ collatzMinPreimage 16 (collatzStep^[t] n))
    (h81 : n % 81 ≠ 10)
    (h9216 : n % 9216 ≠ 1563) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  by_cases hc : ∃ a m : ℕ, 3 * 2 ^ (a + m) ≤ 3 ^ m ∧
      3 ^ m ∣ 2 ^ a * (3 * n + 1) + 1
  · obtain ⟨a, m, hg, hd⟩ := hc
    have hodd : n % 2 = 1 := by omega
    obtain ⟨k, hk, hkn, hmeet⟩ := collatz_smaller_merger_of_odd_run_divisibility n a m hodd hg hd
    exact ⟨k, 1, 2 * m + a, hk, hkn, hmeet.symm⟩
  · apply collatz_coalescence_residual_twentyseven_mod_thirtytwo_without_odd_run_mergers
      n hlarge hclass hmod9 hpreimage h81 h9216
    exact fun a m hg hd => hc ⟨a, m, hg, hd⟩
