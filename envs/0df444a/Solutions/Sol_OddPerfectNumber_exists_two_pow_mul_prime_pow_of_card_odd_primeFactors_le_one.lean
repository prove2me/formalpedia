-- Prove2me | solution 1 for OddPerfectNumber.exists_two_pow_mul_prime_pow_of_card_odd_primeFactors_le_one
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T18:24:27.436235+00:00
-- url     : https://prove2.me/submissions/2ad8a192-59c9-4f55-aff1-80a91788008b

import Mathlib

namespace OddPerfectNumber

theorem _root_.solution (n : Nat) (hn : n ≠ 0)
    (h : (n.primeFactors.erase 2).card ≤ 1) :
    ∃ a q b : Nat, q.Prime ∧ n = 2 ^ a * q ^ b := by
  have hsplit : 2 ^ n.factorization 2 * (n / 2 ^ n.factorization 2) = n :=
    Nat.ordProj_mul_ordCompl_eq_self n 2
  set m := n / 2 ^ n.factorization 2 with hmdef
  have hm0 : m ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hsplit; exact hn hsplit.symm
  have hpf : m.primeFactors = n.primeFactors.erase 2 := by
    rw [← Nat.support_factorization, ← Nat.support_factorization, hmdef,
      Nat.factorization_ordCompl]
    exact Finsupp.support_erase
  by_cases hS : ∃ q, q ∈ n.primeFactors.erase 2
  · obtain ⟨q, hq⟩ := hS
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_erase.1 hq).2
    have hmq : m = q ^ m.primeFactorsList.length := by
      apply Nat.eq_prime_pow_of_unique_prime_dvd hm0
      intro d hd hdm
      have hdS : d ∈ n.primeFactors.erase 2 := by
        rw [← hpf]; exact Nat.mem_primeFactors.2 ⟨hd, hdm, hm0⟩
      exact Finset.card_le_one.1 h d hdS q hq
    exact ⟨n.factorization 2, q, m.primeFactorsList.length, hqp,
      hsplit.symm.trans (congrArg (2 ^ n.factorization 2 * ·) hmq)⟩
  · push_neg at hS
    have hm1 : m = 1 := by
      have he : m.primeFactors = ∅ := by
        rw [hpf]; exact Finset.eq_empty_iff_forall_notMem.2 hS
      rcases Nat.primeFactors_eq_empty.1 he with h0 | h1
      · exact absurd h0 hm0
      · exact h1
    refine ⟨n.factorization 2, 3, 0, Nat.prime_three, ?_⟩
    rw [pow_zero, mul_one]
    calc n = 2 ^ n.factorization 2 * m := hsplit.symm
      _ = 2 ^ n.factorization 2 := by rw [hm1, mul_one]

end OddPerfectNumber
