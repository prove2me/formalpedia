-- Prove2me | solution 1 for SecretaryAdvice.Binary.theorem_19
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T00:53:16.642032+00:00
-- url     : https://prove2.me/submissions/0030f9ae-3c9c-4991-8319-17d1fe26185e

import Mathlib
import Definitions.Def_SecretaryAdvice_Binary_Setting
import Definitions.Def_SecretaryAdvice_Binary_LP
import Theorems.Thm_SecretaryAdvice_Binary_proposition_12_binary
import Theorems.Thm_SecretaryAdvice_Binary_greedy_optimal
import Theorems.Thm_SecretaryAdvice_Binary_greedy_monotone

open SecretaryAdvice.Binary

theorem solution (n : ℕ) (hn : 1 ≤ n) (p p' : ℝ)
    (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1)
    (hp'0 : (1 / 2 : ℝ) ≤ p') (hp'1 : p' ≤ 1) :
    ∃ tY tN : ℕ, 1 ≤ tY ∧ tY ≤ n ∧ 1 ≤ tN ∧ tN ≤ n ∧
      ∀ q : Policy n, ValidPolicy q →
        win p p' q ≤ win p p' (thresholdPolicy n tY tN) :=
  proposition_12_binary n hn p p' hp0 hp1 hp'0 hp'1
    (greedy_optimal n hn p p' hp0 hp1 hp'0 hp'1)
    (greedy_monotone n hn p p' hp0 hp1 hp'0 hp'1)
