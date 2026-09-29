-- Prove2me | solution 1 for OddPerfectNumber.prime_and_exp_mod_sixteen_of_sigma_eq_two_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-08T21:06:35.121553+00:00
-- url     : https://prove2.me/submissions/fc0b70d7-a5a5-4f35-93bc-3cffecee46df

import Mathlib

open Finset

/-- The sum-of-divisors function. -/
private def sig (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

private lemma sig_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    sig (p ^ a) = ∑ i ∈ range (a + 1), p ^ i := by
  rw [sig, Nat.sum_divisors_prime_pow hp]

private lemma sig_prime_pow_succ {p : ℕ} (hp : p.Prime) (a : ℕ) :
    sig (p ^ (a + 1)) = p * sig (p ^ a) + 1 := by
  rw [sig_prime_pow hp, sig_prime_pow hp, geom_sum_succ]

private lemma sig_geom_nat {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (p - 1) * sig (p ^ a) + 1 = p ^ (a + 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, p = d + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  simp only [Nat.add_sub_cancel]
  induction a with
  | zero => simp [sig]
  | succ a ih =>
      rw [sig_prime_pow_succ hp]
      have h : d * ((d + 1) * sig ((d + 1) ^ a) + 1) + 1
          = (d + 1) * (d * sig ((d + 1) ^ a) + 1) := by ring
      rw [h, ih]
      ring

private lemma sig_mod_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (e : ℕ) :
    sig (p ^ e) % 2 = (e + 1) % 2 := by
  have hp1 : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  induction e with
  | zero => simp [sig]
  | succ e ih =>
      rw [sig_prime_pow_succ hp]
      have hm := Nat.mul_mod p (sig (p ^ e)) 2
      rw [hp1, one_mul, Nat.mod_mod_of_dvd] at hm
      · omega
      · exact dvd_rfl

/-- Factorisation of `σ (p ^ (2t-1))` into `σ (p ^ (t-1)) * (p ^ t + 1)`. -/
private lemma sig_factor_half {p t : ℕ} (hp : p.Prime) (ht : 1 ≤ t) :
    sig (p ^ (2 * t - 1)) = sig (p ^ (t - 1)) * (p ^ t + 1) := by
  have hp2 := hp.two_le
  have h1 : (p - 1) * sig (p ^ (t - 1)) + 1 = p ^ t := by
    have h := sig_geom_nat hp (t - 1)
    rwa [show t - 1 + 1 = t by omega] at h
  have h2 : (p - 1) * sig (p ^ (2 * t - 1)) + 1 = (p ^ t) ^ 2 := by
    have h := sig_geom_nat hp (2 * t - 1)
    rw [show 2 * t - 1 + 1 = t * 2 by omega] at h
    rwa [pow_mul] at h
  have hcancel : (p - 1) * sig (p ^ (2 * t - 1))
      = (p - 1) * (sig (p ^ (t - 1)) * (p ^ t + 1)) := by
    have hQ : (p - 1) * (sig (p ^ (t - 1)) * (p ^ t + 1))
        = ((p - 1) * sig (p ^ (t - 1))) * (p ^ t + 1) := by ring
    have hX : ((p - 1) * sig (p ^ (t - 1))) * (p ^ t + 1) + 1 = (p ^ t) ^ 2 := by
      obtain ⟨Q, hQ0⟩ : ∃ Q, Q = (p - 1) * sig (p ^ (t - 1)) := ⟨_, rfl⟩
      rw [← hQ0]
      have hXQ : p ^ t = Q + 1 := by omega
      rw [hXQ]; ring
    omega
  exact Nat.eq_of_mul_eq_mul_left (by omega) hcancel

/-- **Both factors are squares.**  If `σ (p ^ k) = 2 m ^ 2` with `p` an odd prime and
`k ≡ 1 [MOD 4]`, then, writing `k + 1 = 2t`, both `σ (p ^ (t-1))` and `(p ^ t + 1) / 2` are perfect
squares. -/
private theorem exists_sq_of_sig_eq_two_mul_sq {p k m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : k % 4 = 1)
    (h : sig (p ^ k) = 2 * m ^ 2) :
    ∃ t z v : ℕ, k + 1 = 2 * t ∧ t % 2 = 1 ∧ p ^ t + 1 = 2 * z ^ 2 ∧ sig (p ^ (t - 1)) = v ^ 2 := by
  obtain ⟨t, ht⟩ : ∃ t, k + 1 = 2 * t := ⟨(k + 1) / 2, by omega⟩
  have htodd : t % 2 = 1 := by omega
  have ht1 : 1 ≤ t := by omega
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  -- the factorisation
  have hfac : sig (p ^ k) = sig (p ^ (t - 1)) * (p ^ t + 1) := by
    have := sig_factor_half (p := p) (t := t) hp ht1
    rwa [show 2 * t - 1 = k by omega] at this
  -- `W` is odd and divides `p ^ t - 1`
  have hWodd : sig (p ^ (t - 1)) % 2 = 1 := by
    have := sig_mod_two hp hp2 (t - 1)
    rw [show t - 1 + 1 = t by omega] at this
    omega
  have hXodd : p ^ t % 2 = 1 := by
    have : ¬ (2 ∣ p ^ t) := by
      intro hdvd
      have h2p : (2 : ℕ) ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
      have := hp.eq_one_or_self_of_dvd 2 h2p
      omega
    omega
  obtain ⟨Z, hZ⟩ : ∃ Z, p ^ t + 1 = 2 * Z := ⟨(p ^ t + 1) / 2, by omega⟩
  -- the equation becomes `W * Z = m ^ 2`
  have hkey : sig (p ^ (t - 1)) * Z = m ^ 2 := by
    have h1 : 2 * (sig (p ^ (t - 1)) * Z) = 2 * m ^ 2 := by
      rw [← h, hfac, hZ]; ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h1
  -- `W` and `Z` are coprime
  have hWdvd : sig (p ^ (t - 1)) ∣ p ^ t - 1 := by
    have h1 : (p - 1) * sig (p ^ (t - 1)) + 1 = p ^ t := by
      have h := sig_geom_nat hp (t - 1)
      rwa [show t - 1 + 1 = t by omega] at h
    refine ⟨p - 1, ?_⟩
    have hcomm : sig (p ^ (t - 1)) * (p - 1) = (p - 1) * sig (p ^ (t - 1)) := by ring
    omega
  have hcop : Nat.Coprime (sig (p ^ (t - 1))) Z := by
    have hg1 := Nat.gcd_dvd_left (sig (p ^ (t - 1))) Z
    have hg2 := Nat.gcd_dvd_right (sig (p ^ (t - 1))) Z
    have hgm : Nat.gcd (sig (p ^ (t - 1))) Z ∣ p ^ t - 1 := hg1.trans hWdvd
    have hgp : Nat.gcd (sig (p ^ (t - 1))) Z ∣ p ^ t + 1 := hg2.trans ⟨2, by omega⟩
    have hg2' : Nat.gcd (sig (p ^ (t - 1))) Z ∣ 2 := by
      refine (Nat.dvd_add_right hgm).mp ?_
      rwa [show p ^ t - 1 + 2 = p ^ t + 1 by
        have : 1 ≤ p ^ t := Nat.one_le_pow _ _ hp.pos
        omega]
    have hgodd : ¬ (2 ∣ Nat.gcd (sig (p ^ (t - 1))) Z) := by
      intro hev
      have : (2 : ℕ) ∣ sig (p ^ (t - 1)) := hev.trans hg1
      omega
    rcases (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two _ hg2') with h1 | h1
    · exact h1
    · exact absurd (by rw [h1]) hgodd
  -- both factors are squares
  obtain ⟨v, hv⟩ := exists_eq_pow_of_mul_eq_pow
    (Nat.isUnit_iff.mpr hcop) hkey
  obtain ⟨z, hz⟩ := exists_eq_pow_of_mul_eq_pow
    (a := Z) (b := sig (p ^ (t - 1))) (Nat.isUnit_iff.mpr hcop.symm)
    (by rw [← hkey]; ring)
  exact ⟨t, z, v, ht, htodd, by omega, hv⟩

/-- An odd square is `≡ 1 [MOD 8]`. -/
private lemma sq_mod_eight_of_odd {z : ℕ} (hz : z % 2 = 1) : z ^ 2 % 8 = 1 := by
  obtain ⟨c, hc⟩ : ∃ c, z = 2 * c + 1 := ⟨z / 2, by omega⟩
  rcases Nat.even_or_odd c with ⟨d, hd⟩ | ⟨d, hd⟩
  · have : z ^ 2 = 8 * (2 * d ^ 2 + d) + 1 := by rw [hc, hd]; ring
    omega
  · have : z ^ 2 = 8 * (2 * d ^ 2 + 3 * d + 1) + 1 := by rw [hc, hd]; ring
    omega

/-- If `p ^ t ≡ 1 [MOD 16]` with `t` odd and `p` odd, then `p ≡ 1 [MOD 16]`. -/
private lemma mod_sixteen_of_pow_mod_sixteen {p t : ℕ} (hp : p % 2 = 1) (ht : t % 2 = 1)
    (h : p ^ t % 16 = 1) : p % 16 = 1 := by
  have hr4 : (p % 16) ^ 4 % 16 = 1 := by
    have h16 : p % 16 < 16 := Nat.mod_lt _ (by norm_num)
    have hodd : (p % 16) % 2 = 1 := by omega
    interval_cases h : (p % 16) <;> simp_all
  have hred : p ^ t % 16 = (p % 16) ^ (t % 4) % 16 := by
    conv_lhs => rw [Nat.pow_mod, ← Nat.div_add_mod t 4]
    rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, hr4]
    simp [Nat.pow_mod]
  have ht4 : t % 4 = 1 ∨ t % 4 = 3 := by omega
  have h16 : p % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hodd : (p % 16) % 2 = 1 := by omega
  rcases ht4 with h4 | h4 <;> rw [h4] at hred <;> rw [hred] at h <;>
    interval_cases h' : (p % 16) <;> simp_all

/-- The sum `σ (p ^ (t-1)) = 1 + p + ⋯ + p ^ (t-1)` is `≡ t [MOD 8]` when `p ≡ 1 [MOD 8]`. -/
private lemma sig_mod_eight {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 1) (a : ℕ) :
    sig (p ^ a) % 8 = (a + 1) % 8 := by
  induction a with
  | zero => simp [sig]
  | succ a ih =>
      rw [sig_prime_pow_succ hp]
      have hm := Nat.mul_mod p (sig (p ^ a)) 8
      rw [hp8, one_mul, Nat.mod_mod_of_dvd] at hm
      · omega
      · exact dvd_rfl

/-- **If `σ (p ^ k) = 2 m ^ 2` with `p ≡ 1 [MOD 4]` prime and `k ≡ 1 [MOD 4]`, then
`p ≡ 1 [MOD 16]` and `k ≡ 1 [MOD 16]`.** -/
theorem solution (p k m : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hk : k % 4 = 1) (h : (∑ d ∈ (p ^ k).divisors, d) = 2 * m ^ 2) : p % 16 = 1 ∧ k % 16 = 1 := by
  rw [show (∑ d ∈ (p ^ k).divisors, d) = sig (p ^ k) from rfl] at h
  have hp2 : p ≠ 2 := by omega
  obtain ⟨t, z, v, ht, htodd, hz, hv⟩ := exists_sq_of_sig_eq_two_mul_sq hp hp2 hk h
  have hpodd : p % 2 = 1 := by omega
  have hXodd : p ^ t % 2 = 1 := by
    have : ¬ (2 ∣ p ^ t) := by
      intro hdvd
      have h2p : (2 : ℕ) ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
      have := hp.eq_one_or_self_of_dvd 2 h2p
      omega
    omega
  -- `p ^ t ≡ 1 [MOD 4]`, hence `z` is odd
  have hXmod4 : p ^ t % 4 = 1 := by
    have := Nat.pow_mod p t 4
    rw [hp4, one_pow] at this
    omega
  have hzodd : z % 2 = 1 := by
    rcases Nat.even_or_odd z with ⟨d, hd⟩ | hd
    · exfalso
      have hz4 : z ^ 2 = 4 * d ^ 2 := by rw [hd]; ring
      omega
    · exact Nat.odd_iff.mp hd
  have hz8 : z ^ 2 % 8 = 1 := sq_mod_eight_of_odd hzodd
  have hX16 : p ^ t % 16 = 1 := by omega
  have hp16 : p % 16 = 1 := mod_sixteen_of_pow_mod_sixteen hpodd htodd hX16
  refine ⟨hp16, ?_⟩
  -- now `W ≡ t [MOD 8]`, and `W` is an odd square
  have hp8 : p % 8 = 1 := by omega
  have hW8 : sig (p ^ (t - 1)) % 8 = t % 8 := by
    have := sig_mod_eight hp hp8 (t - 1)
    rw [show t - 1 + 1 = t by omega] at this
    exact this
  have hvodd : v % 2 = 1 := by
    have hWodd : sig (p ^ (t - 1)) % 2 = 1 := by
      have := sig_mod_two hp hp2 (t - 1)
      rw [show t - 1 + 1 = t by omega] at this
      omega
    rcases Nat.even_or_odd v with ⟨d, hd⟩ | hd
    · exfalso
      have hv4 : v ^ 2 = 4 * d ^ 2 := by rw [hd]; ring
      omega
    · exact Nat.odd_iff.mp hd
  have hv8 : v ^ 2 % 8 = 1 := sq_mod_eight_of_odd hvodd
  have ht8 : t % 8 = 1 := by omega
  omega

