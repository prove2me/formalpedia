-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_31_absurd
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-13T18:12:38.740827+00:00
-- url     : https://prove2.me/submissions/fe471f93-cc45-41d8-b885-11cc5e4bb3ad

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Basic
set_option autoImplicit false

private theorem sum_divisors_multiple (k q : ℕ) (hk : 0 < k) (hq : 0 < q) :
    q * (∑ d ∈ k.divisors, d) ≤ ∑ d ∈ (k * q).divisors, d := by
  calc
    q * (∑ d ∈ k.divisors, d) = ∑ d ∈ k.divisors.image (fun d => q * d), d := by
      rw [Finset.sum_image]
      · exact Finset.mul_sum _ _ _
      · exact fun _ _ _ _ h => Nat.mul_left_cancel hq h
    _ ≤ ∑ d ∈ (k * q).divisors, d := by
      apply Finset.sum_le_sum_of_subset
      exact fun x hx => match Finset.mem_image.mp hx with
        | ⟨d, hd, he⟩ => he ▸ Nat.mem_divisors.mpr
          ⟨Nat.mul_comm q k ▸ Nat.mul_dvd_mul (dvd_refl q)
            (Nat.mem_divisors.mp hd).1, mul_ne_zero hk.ne' hq.ne'⟩

private theorem fixed_abundant :
    2 * (3 ^ 4 * 5 ^ 2 * 19 ^ 2 * 31 ^ 2) <
      ∑ d ∈ (3 ^ 4 * 5 ^ 2 * 19 ^ 2 * 31 ^ 2 : ℕ).divisors, d := by
  rw [(show Nat.Coprime (3 ^ 4 * 5 ^ 2 * 19 ^ 2) (31 ^ 2) from by decide).sum_divisors_mul,
      (show Nat.Coprime (3 ^ 4 * 5 ^ 2) (19 ^ 2) from by decide).sum_divisors_mul,
      (show Nat.Coprime (3 ^ 4) (5 ^ 2) from by decide).sum_divisors_mul,
      Nat.sum_divisors_prime_pow (show Nat.Prime 3 from by decide),
      Nat.sum_divisors_prime_pow (show Nat.Prime 5 from by decide),
      Nat.sum_divisors_prime_pow (show Nat.Prime 19 from by decide),
      Nat.sum_divisors_prime_pow (show Nat.Prime 31 from by decide)]
  decide

private theorem abundant_of_dvd {k n : ℕ} (hn : n ≠ 0) (hkn : k ∣ n)
    (hab : 2 * k < ∑ d ∈ k.divisors, d) :
    2 * n < ∑ d ∈ n.divisors, d := by
  rcases hkn with ⟨q, rfl⟩
  have hpos : 0 < k ∧ 0 < q :=
    ⟨Nat.pos_of_ne_zero (left_ne_zero_of_mul hn), Nat.pos_of_ne_zero (right_ne_zero_of_mul hn)⟩
  simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    (Nat.mul_lt_mul_of_pos_left hab hpos.2).trans_le (sum_divisors_multiple k q hpos.1 hpos.2)

private theorem half_successor_bound (p : ℕ) : p ≤ 2 * ((p + 1) / 2) := by
  omega

private theorem exp_two_absurd (p m d : ℕ)
    (hp : p.Prime)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : (m ^ 2).primeFactors = {3, 5, 19, 31})
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2) : False := by
  have hn : m ^ 2 ≠ 0 := (Nat.mem_primeFactors.mp h3mem).2.2
  have h13sum := Finset.dvd_prod_of_mem
    (fun q : ℕ => ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i) h3mem
  rw [h3exp, ← Nat.sum_divisors hn] at h13sum
  change 13 ∣ ∑ x ∈ (m ^ 2).divisors, x at h13sum
  have h13not : ¬ 13 ∣ m ^ 2 := fun h =>
    (by decide : 13 ∉ ({3, 5, 19, 31} : Finset ℕ))
      (hsupport ▸ Nat.mem_primeFactors.mpr ⟨by decide, h, hn⟩)
  have hddvd : d ∣ m ^ 2 := hprod.symm ▸ Nat.dvd_mul_left d ((p + 1) / 2)
  have h13p : 13 ∣ p :=
    ((by decide : Nat.Prime 13).dvd_mul.mp (hsig ▸ h13sum)).resolve_right
      (fun hd => h13not (dvd_trans hd hddvd))
  have hp13 : p = 13 := ((Nat.prime_dvd_prime_iff_eq (by decide) hp).mp h13p).symm
  have h7dvd : 7 ∣ m ^ 2 := ⟨d, by simpa [hp13] using hprod⟩
  exact (by decide : 7 ∉ ({3, 5, 19, 31} : Finset ℕ))
    (hsupport ▸ Nat.mem_primeFactors.mpr ⟨by decide, h7dvd, hn⟩)

private theorem square_dvd_of_prime_mem (q m : ℕ) (hq : q.Prime)
    (hmem : q ∈ (m ^ 2).primeFactors) : q ^ 2 ∣ m ^ 2 := by
  exact pow_dvd_pow_of_dvd (hq.dvd_of_dvd_pow (Nat.mem_primeFactors.mp hmem).2.1) 2

private theorem high_exp_absurd (p m d : ℕ)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : (m ^ 2).primeFactors = {3, 5, 19, 31})
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : 4 ≤ (m ^ 2).factorization 3) : False := by
  have hn : m ^ 2 ≠ 0 := (Nat.mem_primeFactors.mp h3mem).2.2
  have hkdiv : (3 ^ 4 * 5 ^ 2 * 19 ^ 2 * 31 ^ 2 : ℕ) ∣ m ^ 2 :=
    (show Nat.Coprime (3 ^ 4 * 5 ^ 2 * 19 ^ 2) (31 ^ 2) from by decide).mul_dvd_of_dvd_of_dvd
      ((show Nat.Coprime (3 ^ 4 * 5 ^ 2) (19 ^ 2) from by decide).mul_dvd_of_dvd_of_dvd
        ((show Nat.Coprime (3 ^ 4) (5 ^ 2) from by decide).mul_dvd_of_dvd_of_dvd
          ((show Nat.Prime 3 from by decide).pow_dvd_iff_le_factorization hn |>.mpr h3exp)
          (square_dvd_of_prime_mem 5 m (by decide) (by simp [hsupport])))
        (square_dvd_of_prime_mem 19 m (by decide) (by simp [hsupport])))
      (square_dvd_of_prime_mem 31 m (by decide) (by simp [hsupport]))
  have hbound := Nat.mul_le_mul_right d (half_successor_bound p)
  rw [Nat.mul_assoc, ← hprod, ← hsig] at hbound
  exact (not_lt_of_ge hbound) (abundant_of_dvd hn hkdiv fixed_abundant)

set_option linter.unusedVariables false in
theorem solution (p m d sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : (m ^ 2).primeFactors = {3, 5, 19, 31})
    (hupper : sigma ≤ 2 * m ^ 2)
    (hsigma : sigma =
      (∑ i ∈ Finset.range ((m ^ 2).factorization 3 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 + 1), 5 ^ i) *
      (∑ i ∈ Finset.range ((m ^ 2).factorization 19 + 1), 19 ^ i) *
      (∑ i ∈ Finset.range ((m ^ 2).factorization 31 + 1), 31 ^ i))
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3pos : 0 < (m ^ 2).factorization 3)
    (h3even : Even ((m ^ 2).factorization 3))
    (h19pos : 0 < (m ^ 2).factorization 19)
    (h19even : Even ((m ^ 2).factorization 19))
    (h31pos : 0 < (m ^ 2).factorization 31)
    (h31even : Even ((m ^ 2).factorization 31)) :
    False := by
  rcases h3even with ⟨a, ha⟩
  exact (show (m ^ 2).factorization 3 = 2 ∨ 4 ≤ (m ^ 2).factorization 3 from by omega).elim
    (exp_two_absurd p m d hp hprod hsig hsupport h3mem)
    (high_exp_absurd p m d hprod hsig hsupport h3mem)
