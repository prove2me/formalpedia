-- Prove2me | solution 1 for WeakGoldbach.two_primes_4e18_add_two
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T03:20:38.886221+00:00
-- url     : https://prove2.me/submissions/071754f1-3932-469e-be1e-35e7a96a6715

import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime

theorem solution :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 4 * 10 ^ 18 + 2 = p + q := by
  refine ⟨653, 3999999999999999349, by norm_num, ?_, by norm_num⟩
  apply lucas_primality _ (6 : ZMod 3999999999999999349)
  · reduce_mod_char
  · intro q hq hqd
    have hfac : 3999999999999999349 - 1 = 2 ^ 2 * 3 ^ 6 * 31 * 61 * 283 * 491 * 5220511 := by
      norm_num
    rw [hfac] at hqd
    have hmem :
        q = 2 ∨ q = 3 ∨ q = 31 ∨ q = 61 ∨ q = 283 ∨ q = 491 ∨ q = 5220511 := by
      rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
      swap
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      swap
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
          (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      swap
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
          (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      swap
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <|
          (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      swap
      · exact Or.inr <| Or.inr <| Or.inl <|
          (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · exact Or.inl <|
          (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)
      · exact Or.inr <| Or.inl <|
          (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (reduce_mod_char; decide)
