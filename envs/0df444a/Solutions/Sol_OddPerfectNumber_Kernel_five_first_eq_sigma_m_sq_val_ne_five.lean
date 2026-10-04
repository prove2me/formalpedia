-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_first_eq_sigma_m_sq_val_ne_five
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T09:00:43.146159+00:00
-- url     : https://prove2.me/submissions/6eabeab4-130b-45bd-ad32-9719e0dd0e54

import Mathlib

section Helpers5505

open ArithmeticFunction in
theorem split7_5505 (a b c d e f g : ℕ) (h1 : Nat.Coprime (a * b * c * d * e * f) g)
    (h2 : Nat.Coprime (a * b * c * d * e) f) (h3 : Nat.Coprime (a * b * c * d) e)
    (h4 : Nat.Coprime (a * b * c) d) (h5 : Nat.Coprime (a * b) c) (h6 : Nat.Coprime a b) :
    sigma 1 (a * b * c * d * e * f * g) =
      sigma 1 a * sigma 1 b * sigma 1 c * sigma 1 d * sigma 1 e * sigma 1 f * sigma 1 g := by
  rw [isMultiplicative_sigma.map_mul_of_coprime h1, isMultiplicative_sigma.map_mul_of_coprime h2,
    isMultiplicative_sigma.map_mul_of_coprime h3, isMultiplicative_sigma.map_mul_of_coprime h4,
    isMultiplicative_sigma.map_mul_of_coprime h5, isMultiplicative_sigma.map_mul_of_coprime h6]

open ArithmeticFunction in
theorem sig_3_5505 : sigma 1 (3 ^ 2) = 13 := by
  rw [sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

open ArithmeticFunction in
theorem sig_7_5505 : sigma 1 (7 ^ 2) = 57 := by
  rw [sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

open ArithmeticFunction in
theorem sig_31_5505 : sigma 1 (31 ^ 4) = 954305 := by
  rw [sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

open ArithmeticFunction in
theorem sig_11_5505 : sigma 1 (11 ^ 4) = 16105 := by
  rw [sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

open ArithmeticFunction in
theorem sig_41_5505 : sigma 1 (41 ^ 4) = 2896405 := by
  rw [sigma_one_apply_prime_pow (by norm_num : Nat.Prime 41)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

open ArithmeticFunction in
theorem sig_61_5505 : sigma 1 (61 ^ 4) = 14076605 := by
  rw [sigma_one_apply_prime_pow (by norm_num : Nat.Prime 61)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

open ArithmeticFunction in
theorem sig_71_5505 : sigma 1 (71 ^ 4) = 25774705 := by
  rw [sigma_one_apply_prime_pow (by norm_num : Nat.Prime 71)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

open ArithmeticFunction in
theorem sigma_val_5505 :
    (∑ d ∈ ((76996703805577941 : ℕ) ^ 2).divisors, d) =
      13 * 57 * 954305 * 16105 * 2896405 * 14076605 * 25774705 := by
  have hsq : (76996703805577941 : ℕ) ^ 2 =
      3 ^ 2 * 7 ^ 2 * 31 ^ 4 * 11 ^ 4 * 41 ^ 4 * 61 ^ 4 * 71 ^ 4 := by norm_num
  have c1 : Nat.Coprime (3 ^ 2 * 7 ^ 2 * 31 ^ 4 * 11 ^ 4 * 41 ^ 4 * 61 ^ 4) (71 ^ 4) := by norm_num
  have c2 : Nat.Coprime (3 ^ 2 * 7 ^ 2 * 31 ^ 4 * 11 ^ 4 * 41 ^ 4) (61 ^ 4) := by norm_num
  have c3 : Nat.Coprime (3 ^ 2 * 7 ^ 2 * 31 ^ 4 * 11 ^ 4) (41 ^ 4) := by norm_num
  have c4 : Nat.Coprime (3 ^ 2 * 7 ^ 2 * 31 ^ 4) (11 ^ 4) := by norm_num
  have c5 : Nat.Coprime (3 ^ 2 * 7 ^ 2) (31 ^ 4) := by norm_num
  have c6 : Nat.Coprime (3 ^ 2) (7 ^ 2) := by norm_num
  rw [← sigma_one_apply, hsq, split7_5505 _ _ _ _ _ _ _ c1 c2 c3 c4 c5 c6,
    sig_3_5505, sig_7_5505, sig_31_5505, sig_11_5505, sig_41_5505, sig_61_5505, sig_71_5505]

theorem fact_val_5505 :
    (13 * 57 * 954305 * 16105 * 2896405 * 14076605 * 25774705 : ℕ).factorization 5 = 5 := by
  have h : (13 * 57 * 954305 * 16105 * 2896405 * 14076605 * 25774705 : ℕ) =
      5 ^ 5 * 3829720069979695394118538369161 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5)]
  rw [Finsupp.add_apply, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem key_5505 :
    (∑ d ∈ ((76996703805577941 : ℕ) ^ 2).divisors, d).factorization 5 = 5 := by
  rw [sigma_val_5505, fact_val_5505]

end Helpers5505

theorem solution : ¬ (∀ (p m d1 q r : Nat) (hp : p.Prime)
    (hp2 : p != 2) (hp4 : p % 4 = 1) (hpm : Not (Dvd.dvd p m)) (hqr : q < r)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r))),
    (∑ d ∈ (m ^ 2).divisors, d).factorization p ≠ 5) := by
  intro h
  exact h 5 76996703805577941 118274506613791 7 31 (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) key_5505
