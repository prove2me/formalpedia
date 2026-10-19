-- Prove2me | solution 1 for PrimeSum.sum_primes_card_le_log_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-18T14:51:58.300681+00:00
-- url     : https://prove2.me/submissions/e0c0509c-c3dc-4cd3-bab0-232f647a4d28

import Mathlib
import Theorems.Thm_PrimeSum_log_halving

theorem solution (n : ℕ) (hn : 2 ≤ n) :
    ∃ s : Multiset ℕ, (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n ∧ s.card ≤ Nat.log 2 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n 4 with h4 | h4
    · interval_cases n
      · exact ⟨{2}, by decide, by decide, by decide⟩
      · exact ⟨{3}, by decide, by decide, by decide⟩
    · obtain ⟨q, hqP, hqgt, hqle⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
      have hqn : q ≤ n := by omega
      have h2q : n < 2 * q := by omega
      rcases Nat.lt_or_ge 1 (n - q) with h1 | h1
      · obtain ⟨s, hsP, hsum, hcard⟩ := ih (n - q) (by omega) (by omega)
        refine ⟨s + {q}, ?_, ?_, ?_⟩
        · intro p hp
          rcases Multiset.mem_add.1 hp with h' | h'
          · exact hsP p h'
          · rw [Multiset.mem_singleton] at h'
            rw [h']
            exact hqP
        · rw [Multiset.sum_add, Multiset.sum_singleton, hsum]
          omega
        · rw [Multiset.card_add, Multiset.card_singleton]
          have := PrimeSum.log_halving n q (by omega) h2q hqn
          omega
      · interval_cases h : n - q
        · have hnq : n = q := by omega
          refine ⟨{n}, ?_, ?_, ?_⟩
          · intro p hp
            rw [Multiset.mem_singleton] at hp
            rw [hp, hnq]
            exact hqP
          · simp
          · simp only [Multiset.card_singleton]
            have := Nat.le_log_of_pow_le (b := 2) (x := 1) (y := n) (by norm_num)
              (by omega : 2 ^ 1 ≤ n)
            omega
        · obtain ⟨q2, h2P, h2gt, h2le⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2 - 1) (by omega)
          have hqodd : Odd q := hqP.odd_of_ne_two (by omega)
          obtain ⟨k, hk⟩ := hqodd
          have h2n : q2 ≤ n - 2 := by omega
          have h2ge : n / 2 ≤ q2 := by omega
          rcases Nat.lt_or_ge (n / 2) q2 with hlt | hle
          · obtain ⟨s, hsP, hsum, hcard⟩ := ih (n - q2) (by omega) (by omega)
            refine ⟨s + {q2}, ?_, ?_, ?_⟩
            · intro p hp
              rcases Multiset.mem_add.1 hp with h' | h'
              · exact hsP p h'
              · rw [Multiset.mem_singleton] at h'
                rw [h']
                exact h2P
            · rw [Multiset.sum_add, Multiset.sum_singleton, hsum]
              omega
            · rw [Multiset.card_add, Multiset.card_singleton]
              have := PrimeSum.log_halving n q2 (by omega) (by omega) (by omega)
              omega
          · have hqn2 : q2 = n / 2 := le_antisymm hle h2ge
            have hne : n = q2 + q2 := by omega
            have h3 : 2 ≤ q2 := h2P.two_le
            refine ⟨Multiset.replicate 2 q2, ?_, ?_, ?_⟩
            · intro p hp
              rw [Multiset.mem_replicate] at hp
              rw [hp.2]
              exact h2P
            · rw [Multiset.sum_replicate, nsmul_eq_mul]
              omega
            · rw [Multiset.card_replicate]
              have := Nat.le_log_of_pow_le (b := 2) (x := 2) (y := n) (by norm_num)
                (by omega : 2 ^ 2 ≤ n)
              omega
