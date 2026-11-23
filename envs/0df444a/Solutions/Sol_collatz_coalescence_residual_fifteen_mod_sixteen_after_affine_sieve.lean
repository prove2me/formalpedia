-- Prove2me | solution 1 for collatz_coalescence_residual_fifteen_mod_sixteen_after_affine_sieve
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Siyuan Chen
-- created : 2026-11-23T15:13:59.391707+00:00
-- url     : https://prove2.me/submissions/4f2f5dc1-73a7-4967-8c81-df34202162b4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_collatz_min_preimage_lt_iff
import Theorems.Thm_collatz_coalescence_residual_fifteen_mod_sixteen_after_preimage_sieve

theorem solution (n : ℕ)
    (hlarge : 2310000 ≤ n) (hclass : n % 16 = 15)
    (hmod9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7)
    (hprefix : ∀ t : ℕ, t ≤ 128 → n ≤ collatzStep^[t] n)
    (h81 : n % 81 ≠ 10)
    (h2304 : n % 2304 ≠ 1743 ∧ n % 2304 ≠ 1599)
    (h4608 : n % 4608 ≠ 2847 ∧ n % 4608 ≠ 735 ∧ n % 4608 ≠ 991 ∧
      n % 4608 ≠ 2527 ∧ n % 4608 ≠ 3039 ∧ n % 4608 ≠ 4575) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  by_cases h : ∃ t : ℕ, t ≤ 128 ∧ collatzMinPreimage 16 (collatzStep^[t] n) < n
  · obtain ⟨t, ht, hlt⟩ := h
    have hpos : 0 < collatzStep^[t] n := by
      have := hprefix t ht
      omega
    obtain ⟨k, b, hk, hkn, _, heq⟩ := (collatz_min_preimage_lt_iff 16 _ n hpos).mp hlt
    exact ⟨k, t, b, hk, hkn, heq.symm⟩
  · exact collatz_coalescence_residual_fifteen_mod_sixteen_after_preimage_sieve n hlarge hclass hmod9
      (fun t ht => Nat.le_of_not_lt fun hlt => h ⟨t, ht, hlt⟩)
      h81 h2304 h4608
