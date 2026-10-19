-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_two_prime_index_three_exponent_one_gives_thirteen_dvd_d1
-- status  : ACCEPTED   (prove)
-- author  : @zsuhail
-- created : 2026-10-16T17:07:20.046989+00:00
-- url     : https://prove2.me/submissions/0b23986d-2a0e-4c69-8eed-5adb9950030a

import Theorems.Thm_OddPerfectNumber_Kernel_five_two_prime_index_three_exponent_one_gives_thirteen_dvd_d1_given_index_primes_ne_thirteen
import Theorems.Thm_OddPerfectNumber_Kernel_five_two_prime_index_not_three_mod_twelve
import Theorems.Thm_OddPerfectNumber_Kernel_five_two_prime_cyclotomic_split

namespace OddPerfectNumber.Kernel.ThirteenExclusionAux

/-- Coprime factors of a square in `ℕ` are squares. -/
theorem sq_of_coprime_mul {a b c : ℕ} (hab : Nat.Coprime a b) (h : a * b = c ^ 2) :
    ∃ d, a = d ^ 2 :=
  exists_eq_pow_of_mul_eq_pow
    (by rw [gcd_eq_nat_gcd, Nat.Coprime.gcd_eq_one hab]; exact isUnit_one) h

/-- Squares are `0`, `1` or `4` modulo `8`. -/
theorem sq_mod_eight (g : ℕ) : g ^ 2 % 8 = 0 ∨ g ^ 2 % 8 = 1 ∨ g ^ 2 % 8 = 4 := by
  rw [Nat.pow_mod]
  have h : g % 8 < 8 := Nat.mod_lt _ (by norm_num)
  generalize g % 8 = r at h ⊢
  interval_cases r <;> decide

/-- Residues forced by `p ≡ 5 (mod 12)`: `p² - p + 1 = 3W` with `W ≡ 1 (mod 3)` and
`W ≡ 3, 7 (mod 8)`, and `p² + p + 1 ≡ 3, 7 (mod 8)`. -/
theorem p_facts {p : ℕ} (hp12 : p % 12 = 5) :
    3 * ((p ^ 2 - p + 1) / 3) = p ^ 2 - p + 1 ∧ ((p ^ 2 - p + 1) / 3) % 3 = 1 ∧
    (((p ^ 2 - p + 1) / 3) % 8 = 3 ∨ ((p ^ 2 - p + 1) / 3) % 8 = 7) ∧
    ((p ^ 2 + p + 1) % 8 = 3 ∨ (p ^ 2 + p + 1) % 8 = 7) := by
  have hle : p ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p
  have hs : p ^ 2 % 72 = (p % 72) ^ 2 % 72 := Nat.pow_mod p 2 72
  have hc : p % 72 = 5 ∨ p % 72 = 17 ∨ p % 72 = 29 ∨ p % 72 = 41 ∨ p % 72 = 53 ∨
      p % 72 = 65 := by omega
  rcases hc with h | h | h | h | h | h <;> rw [h] at hs <;> norm_num at hs <;> omega

/-- `W = (p² - p + 1)/3` is coprime to `(p + 1)/2`. -/
theorem W_coprime {p W : ℕ} (hp : p.Prime) (hW : 3 * W = p ^ 2 - p + 1) (hW3 : W % 3 = 1)
    (h2 : 2 ∣ p + 1) : Nat.Coprime W ((p + 1) / 2) := by
  apply Nat.coprime_of_dvd
  intro k hk hkW hkY
  have hkY' : k ∣ p + 1 := hkY.trans (Nat.div_dvd_of_dvd h2)
  have hkZ : k ∣ p ^ 2 - p + 1 := by
    rw [← hW]; exact Dvd.dvd.mul_left hkW 3
  have hle : p ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p
  have hsq : (p + 1) ^ 2 = (p ^ 2 - p + 1) + 3 * p := by
    have e : (p + 1) ^ 2 = p ^ 2 + 2 * p + 1 := by ring
    rw [e]; omega
  have h3p : k ∣ 3 * p := by
    have h1 : k ∣ (p + 1) ^ 2 := dvd_pow hkY' two_ne_zero
    rw [hsq] at h1
    exact (Nat.dvd_add_right hkZ).mp h1
  rcases (Nat.Prime.dvd_mul hk).mp h3p with h | h
  · have hk3 : k = 3 := (Nat.prime_dvd_prime_iff_eq hk Nat.prime_three).mp h
    subst hk3
    omega
  · have hkp : k = p := (Nat.prime_dvd_prime_iff_eq hk hp).mp h
    subst hkp
    have h1 : k ∣ 1 := (Nat.dvd_add_right (dvd_refl k)).mp hkY'
    exact hk.one_lt.ne' (Nat.dvd_one.mp h1)

/-- The index prime carried by `p² + p + 1` is not `13`. -/
theorem first_ne_thirteen {p t x : ℕ} (hp12 : p % 12 = 5) (hX : p ^ 2 + p + 1 = t * x ^ 2) :
    t ≠ 13 := by
  intro h
  subst h
  have h1 := (p_facts hp12).2.2.2
  have h2 := sq_mod_eight x
  omega

/-- The index prime not carried by `p² + p + 1` is not `13`. -/
theorem other_ne_thirteen (p x d1 t t' m : ℕ) (hp : p.Prime) (hp12 : p % 12 = 5)
    (hX : p ^ 2 + p + 1 = t * x ^ 2)
    (hm2 : m ^ 2 = (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1)) * (d1 ^ 2 * (t * t')))
    (hm0 : m ≠ 0) : t' ≠ 13 := by
  intro ht'
  subst ht'
  obtain ⟨hW, hW3, hW8, -⟩ := p_facts hp12
  generalize hWdef : (p ^ 2 - p + 1) / 3 = W at hW hW3 hW8
  have h2 : 2 ∣ p + 1 := by omega
  have hcopWY : Nat.Coprime W ((p + 1) / 2) := W_coprime hp hW hW3 h2
  -- `m² = (t x d1)² · ((p+1)/2 · 3W · 13)`
  have hsq : (t * x * d1) ^ 2 * ((p + 1) / 2 * (3 * W) * 13) = m ^ 2 := by
    rw [hm2, hX, hW]; ring
  have hd0 : t * x * d1 ≠ 0 := by
    intro h0
    have : m ^ 2 = 0 := by rw [← hsq, h0]; ring
    exact hm0 (pow_eq_zero_iff two_ne_zero |>.mp this)
  have hdm : t * x * d1 ∣ m := (Nat.pow_dvd_pow_iff two_ne_zero).mp ⟨_, hsq.symm⟩
  obtain ⟨k, hk⟩ := hdm
  have hS : (p + 1) / 2 * (3 * W) * 13 = k ^ 2 := by
    have e : (t * x * d1) ^ 2 * ((p + 1) / 2 * (3 * W) * 13) = (t * x * d1) ^ 2 * k ^ 2 := by
      rw [hsq, hk]; ring
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.pos_of_ne_zero hd0) 2) e
  have hW3' : Nat.Coprime W 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]; omega
  have hp13 : Nat.Prime 13 := by norm_num
  by_cases h13 : 13 ∣ W
  · -- `W·13` and `3·(p+1)/2` are coprime with square product, so `W·13` is a square.
    have h13Y : Nat.Coprime 13 (3 * ((p + 1) / 2)) := by
      rw [Nat.Prime.coprime_iff_not_dvd hp13]
      intro h
      rcases (Nat.Prime.dvd_mul hp13).mp h with h | h
      · omega
      · have hc : Nat.Coprime 13 ((p + 1) / 2) := Nat.Coprime.coprime_dvd_left h13 hcopWY
        exact (Nat.Prime.coprime_iff_not_dvd hp13).mp hc h
    have hcop : Nat.Coprime (W * 13) (3 * ((p + 1) / 2)) :=
      Nat.Coprime.mul_left (Nat.Coprime.mul_right hW3' hcopWY) h13Y
    have heq : (W * 13) * (3 * ((p + 1) / 2)) = k ^ 2 := by rw [← hS]; ring
    obtain ⟨g, hg⟩ := sq_of_coprime_mul hcop heq
    have hg8 := sq_mod_eight g
    omega
  · -- `W` and `3·(p+1)/2·13` are coprime with square product, so `W` is a square.
    have hW13 : Nat.Coprime W 13 :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp13).mpr h13)
    have hcop : Nat.Coprime W (3 * ((p + 1) / 2) * 13) :=
      Nat.Coprime.mul_right (Nat.Coprime.mul_right hW3' hcopWY) hW13
    have heq : W * (3 * ((p + 1) / 2) * 13) = k ^ 2 := by rw [← hS]; ring
    obtain ⟨g, hg⟩ := sq_of_coprime_mul hcop heq
    have hg8 := sq_mod_eight g
    omega

end OddPerfectNumber.Kernel.ThirteenExclusionAux

open OddPerfectNumber.Kernel OddPerfectNumber.Kernel.ThirteenExclusionAux in
theorem solution (p m d1 q r : Nat)
    (hp : p.Prime) (hp2 : p != 2) (hp4 : p % 4 = 1) (hm : Odd m)
    (hpm : Not (Dvd.dvd p m)) (hq : q.Prime) (hr : r.Prime) (hqr : q < r)
    (hq3 : q != 3) (hr3 : r != 3)
    (h1 : 2 * m ^ 2 =
      (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r)))
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r)))
    (he : m.factorization 3 = 1) :
    Dvd.dvd 13 d1 := by
  have hp12 : p % 12 = 5 :=
    five_two_prime_index_not_three_mod_twelve p m d1 q r hp hp2 hp4 hm hpm hq hr hqr hq3 hr3 h1
  have hm0 : m ≠ 0 := by
    obtain ⟨j, hj⟩ := hm
    omega
  have hm2 : m ^ 2 = (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1)) * (d1 ^ 2 * (q * r)) := by
    have e : 2 * m ^ 2 =
        2 * ((p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1)) * (d1 ^ 2 * (q * r))) := by
      rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) e
  have hqr13 : q ≠ 13 ∧ r ≠ 13 := by
    rcases five_two_prime_cyclotomic_split p m d1 q r hp hp2 hp4 hm hpm hq hr hqr h1 with
      ⟨x, hx⟩ | ⟨x, hx⟩
    · exact ⟨first_ne_thirteen hp12 hx, other_ne_thirteen p x d1 q r m hp hp12 hx hm2 hm0⟩
    · refine ⟨other_ne_thirteen p x d1 r q m hp hp12 hx (by rw [hm2]; ring) hm0,
        first_ne_thirteen hp12 hx⟩
  have hp13 : p ≠ 13 := by omega
  exact five_two_prime_index_three_exponent_one_gives_thirteen_dvd_d1_given_index_primes_ne_thirteen
    p m d1 q r hp hp4 hm hpm hq hr hqr hq3 hr3 (bne_iff_ne.mpr hp13) (bne_iff_ne.mpr hqr13.1)
    (bne_iff_ne.mpr hqr13.2) he h2
