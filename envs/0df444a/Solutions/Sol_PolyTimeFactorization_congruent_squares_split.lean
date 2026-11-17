-- Prove2me | solution 1 for PolyTimeFactorization.congruent_squares_split
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T21:07:59.756691+00:00
-- url     : https://prove2.me/submissions/6b17d396-2e86-4520-9ac5-57cee0dc57ae

import Mathlib
namespace PolyTimeFactorization

theorem congruent_squares_split (n : ℕ) (x y : ℤ) (hn : 0 < n)
    (hsq : (n : ℤ) ∣ x ^ 2 - y ^ 2)
    (hxy : ¬ (n : ℤ) ∣ x - y) (hxy' : ¬ (n : ℤ) ∣ x + y) :
    1 < Int.gcd (x - y) (n : ℤ) ∧ Int.gcd (x - y) (n : ℤ) < n := by
  have hgpos : 0 < Int.gcd (x - y) (n : ℤ) :=
    Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast hn.ne')
  have hgn : Int.gcd (x - y) (n : ℤ) ∣ n := by
    have := Int.gcd_dvd_right (x - y) (n : ℤ)
    exact Int.natCast_dvd_natCast.mp (by simpa using this)
  constructor
  · by_contra h
    have h1 : Int.gcd (x - y) (n : ℤ) = 1 := by omega
    have hcop : IsCoprime (n : ℤ) (x - y) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]; exact h1
    apply hxy'
    have : (n : ℤ) ∣ (x - y) * (x + y) := by
      have e : (x - y) * (x + y) = x ^ 2 - y ^ 2 := by ring
      rw [e]; exact hsq
    exact hcop.dvd_of_dvd_mul_left this
  · rcases lt_or_eq_of_le (Nat.le_of_dvd hn hgn) with h | h
    · exact h
    · exfalso
      apply hxy
      have := Int.gcd_dvd_left (x - y) (n : ℤ)
      rw [h] at this
      exact this

end PolyTimeFactorization

theorem solution (n : ℕ) (x y : ℤ) (hn : 0 < n)
    (hsq : (n : ℤ) ∣ x ^ 2 - y ^ 2)
    (hxy : ¬ (n : ℤ) ∣ x - y) (hxy' : ¬ (n : ℤ) ∣ x + y) :
    1 < Int.gcd (x - y) (n : ℤ) ∧ Int.gcd (x - y) (n : ℤ) < n :=
  PolyTimeFactorization.congruent_squares_split n x y hn hsq hxy hxy'
