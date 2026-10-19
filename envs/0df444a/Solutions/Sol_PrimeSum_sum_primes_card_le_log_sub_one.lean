-- Prove2me | solution 1 for PrimeSum.sum_primes_card_le_log_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-18T14:51:59.216799+00:00
-- url     : https://prove2.me/submissions/022a7a7a-79cb-4e1f-8e94-46894b42e266

import Mathlib
import Theorems.Thm_PrimeSum_log_halving

theorem solution (n : ℕ) (hn : 7 ≤ n) :
    ∃ s : Multiset ℕ, (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n ∧ s.card ≤ Nat.log 2 n - 1 := by
  -- small numbers: two summands always suffice below 7, so the only work is 7 to 15
  have small : ∀ m : ℕ, 2 ≤ m → m ≤ 6 →
      ∃ s : Multiset ℕ, (∀ p ∈ s, Nat.Prime p) ∧ s.sum = m ∧ s.card ≤ 2 := by
    intro m h2 h6
    interval_cases m
    · exact ⟨{2}, by decide, by decide, by decide⟩
    · exact ⟨{3}, by decide, by decide, by decide⟩
    · exact ⟨{2, 2}, by decide, by decide, by decide⟩
    · exact ⟨{5}, by decide, by decide, by decide⟩
    · exact ⟨{3, 3}, by decide, by decide, by decide⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n 16 with h16 | h16
    · interval_cases n
      · exact ⟨{7}, by decide, by decide, by decide⟩
      · exact ⟨{3, 5}, by decide, by decide, by decide⟩
      · exact ⟨{2, 7}, by decide, by decide, by decide⟩
      · exact ⟨{3, 7}, by decide, by decide, by decide⟩
      · exact ⟨{11}, by decide, by decide, by decide⟩
      · exact ⟨{5, 7}, by decide, by decide, by decide⟩
      · exact ⟨{13}, by decide, by decide, by decide⟩
      · exact ⟨{3, 11}, by decide, by decide, by decide⟩
      · exact ⟨{2, 13}, by decide, by decide, by decide⟩
    · have hlog4 : 4 ≤ Nat.log 2 n :=
        Nat.le_log_of_pow_le (b := 2) (x := 4) (y := n) (by norm_num) (by omega)
      obtain ⟨q, hqP, hqgt, hqle⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
      have hqn : q ≤ n := by omega
      have h2q : n < 2 * q := by omega
      rcases Nat.lt_or_ge 1 (n - q) with h1 | h1
      · rcases Nat.lt_or_ge (n - q) 7 with hm7 | hm7
        · -- the remainder is one of 2..6: three summands in total
          obtain ⟨s, hsP, hsum, hcard⟩ := small (n - q) (by omega) (by omega)
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
            omega
        · -- the remainder is at least 7: recurse
          obtain ⟨s, hsP, hsum, hcard⟩ := ih (n - q) (by omega) hm7
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
        · -- n is itself prime
          have hnq : n = q := by omega
          refine ⟨{n}, ?_, ?_, ?_⟩
          · intro p hp
            rw [Multiset.mem_singleton] at hp
            rw [hp, hnq]
            exact hqP
          · simp
          · simp only [Multiset.card_singleton]
            omega
        · -- remainder 1: q = n - 1 is prime and n is even, so try a prime near n/2
          obtain ⟨q2, h2P, h2gt, h2le⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2 - 1) (by omega)
          have hqodd : Odd q := hqP.odd_of_ne_two (by omega)
          obtain ⟨k, hk⟩ := hqodd
          have h2n : q2 ≤ n - 2 := by omega
          have h2ge : n / 2 ≤ q2 := by omega
          rcases Nat.lt_or_ge (n / 2) q2 with hlt | hle
          · rcases Nat.lt_or_ge (n - q2) 7 with hm7 | hm7
            · -- remainder one of 2..6: three summands
              obtain ⟨s, hsP, hsum, hcard⟩ := small (n - q2) (by omega) (by omega)
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
                omega
            · obtain ⟨s, hsP, hsum, hcard⟩ := ih (n - q2) (by omega) hm7
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
          · -- q2 = n/2, so n = q2 + q2
            have hqn2 : q2 = n / 2 := le_antisymm hle h2ge
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
              omega
