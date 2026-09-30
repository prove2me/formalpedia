-- Prove2me | solution 1 for WeakGoldbach.verified_three_odd_primes_to_8875e30
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T14:33:01.129518+00:00
-- url     : https://prove2.me/submissions/396d539d-9257-4394-941a-8f5c2b4a28a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_verified_two_odd_primes_to_4e18
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_to_8875e30
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime

theorem solution (n : ℕ)
    (hlo : 9 ≤ n) (hhi : n ≤ 8875694145621773516800000000000) (hodd : Odd n) :
    ∃ p q r : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r := by
  have hr1 : Nat.Prime 3999999999999999349 := by
    apply lucas_primality _ (6 : ZMod 3999999999999999349)
    · reduce_mod_char
    · intro q hq hqd
      have hfac : 3999999999999999349 - 1
          = 2 ^ 2 * 3 ^ 6 * 31 * 61 * 283 * 491 * 5220511 := by
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
  have hr2 : Nat.Prime 3999999999999998833 := by
    apply lucas_primality _ (5 : ZMod 3999999999999998833)
    · reduce_mod_char
    · intro q hq hqd
      have hfac : 3999999999999998833 - 1
          = 2 ^ 4 * 3 * 89 * 5889811 * 158974471 := by
        norm_num
      rw [hfac] at hqd
      have hmem :
          q = 2 ∨ q = 3 ∨ q = 89 ∨ q = 5889811 ∨ q = 158974471 := by
        rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
        swap
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <|
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
        swap
        · exact Or.inr <| Or.inl <|
            (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        exact Or.inl <|
          (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)
      rcases hmem with rfl | rfl | rfl | rfl | rfl <;>
        (reduce_mod_char; decide)
  have h653 : Nat.Prime 653 := by norm_num
  have h1171 : Nat.Prime 1171 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  have h3 : Nat.Prime 3 := by norm_num
  have ⟨k, hk⟩ := hodd
  by_cases hsmall : n ≤ 4 * 10 ^ 18 + 3
  · obtain ⟨a, b, ha, hb, hao, hbo, hsum⟩ :=
      WeakGoldbach.verified_two_odd_primes_to_4e18 (n - 3) (by omega)
        (by omega) ⟨k - 1, by omega⟩
    exact ⟨3, a, b, h3, ha, hb, ⟨1, rfl⟩, hao, hbo, by omega⟩
  by_cases hb5 : n = 4 * 10 ^ 18 + 5
  · refine ⟨3, 653, 3999999999999999349, h3, h653, hr1,
      ⟨1, rfl⟩, ⟨326, rfl⟩, ⟨1999999999999999674, rfl⟩, ?_⟩
    omega
  by_cases hb7 : n = 4 * 10 ^ 18 + 7
  · refine ⟨5, 653, 3999999999999999349, h5, h653, hr1,
      ⟨2, rfl⟩, ⟨326, rfl⟩, ⟨1999999999999999674, rfl⟩, ?_⟩
    omega
  · obtain ⟨p, hpx, hpn, hpP⟩ :=
      WeakGoldbach.prime_in_4e18_window_to_8875e30 (n - 4 * 10 ^ 18 - 6)
        (by omega)
    have hpo : Odd p := hpP.odd_of_ne_two (by omega)
    have ⟨j, hj⟩ := hpo
    have hmp : Even (n - p) := ⟨k - j, by omega⟩
    have ⟨w, hw⟩ := hmp
    by_cases hm : n - p ≤ 4 * 10 ^ 18
    · obtain ⟨a, b, ha, hb, hao, hbo, hsum⟩ :=
        WeakGoldbach.verified_two_odd_primes_to_4e18 (n - p) (by omega) hm ⟨w, hw⟩
      exact ⟨p, a, b, hpP, ha, hb, hpo, hao, hbo, by omega⟩
    · by_cases hm2 : n - p = 4 * 10 ^ 18 + 2
      · refine ⟨p, 653, 3999999999999999349, hpP, h653, hr1,
          hpo, ⟨326, rfl⟩, ⟨1999999999999999674, rfl⟩, ?_⟩
        omega
      · refine ⟨p, 1171, 3999999999999998833, hpP, h1171, hr2,
          hpo, ⟨585, rfl⟩, ⟨1999999999999999416, rfl⟩, ?_⟩
        omega
