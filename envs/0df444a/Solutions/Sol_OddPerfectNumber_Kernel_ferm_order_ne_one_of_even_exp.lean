-- Prove2me | solution 1 for OddPerfectNumber.Kernel.ferm_order_ne_one_of_even_exp
-- status  : ACCEPTED   (disprove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:19:41.121984+00:00
-- url     : https://prove2.me/submissions/1e94155e-bf10-44ba-8e4a-5855c3e211a3

import Mathlib

theorem solution : ¬ (∀ {p m t : Nat}, p.Prime → (¬ Dvd.dvd p m) →
    (∃ v : ℕ, p - 1 = 2 ^ v) → p ≥ 5 → Dvd.dvd t (m ^ 2) →
    0 < (m ^ 2).factorization t →
    ¬ Dvd.dvd p (∑ i ∈ Finset.range ((m ^ 2).factorization t + 1), t ^ i)) := by
  intro h
  have hf : (121 ^ 2 : Nat).factorization 11 = 4 := by
    have heq : (121 ^ 2 : Nat) = 11 ^ 4 := by norm_num
    rw [heq, Nat.factorization_pow_self (by norm_num : Nat.Prime 11)]
  have hbad := @h 5 121 11 (by norm_num) (by norm_num) ⟨2, by norm_num⟩
    (by norm_num) (by norm_num) (by rw [hf]; norm_num)
  apply hbad
  rw [hf]
  norm_num [Finset.sum_range_succ]
