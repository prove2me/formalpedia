-- Prove2me | solution 1 for OddPerfectNumber.special_pow_lt_sq_of_exponent_ge_five
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-08T21:38:15.735209+00:00
-- url     : https://prove2.me/submissions/4febef83-4166-4d00-a664-f12f61cb1ed1

import Mathlib

set_option autoImplicit false

open Finset

variable {p k m : ℕ}

/-- The sum-of-divisors function. -/
private def sig (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

private lemma sig_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    sig (p ^ a) = ∑ i ∈ range (a + 1), p ^ i := by
  rw [sig, Nat.sum_divisors_prime_pow hp]

private lemma sig_prime_pow_succ {p : ℕ} (hp : p.Prime) (a : ℕ) :
    sig (p ^ (a + 1)) = p * sig (p ^ a) + 1 := by
  rw [sig_prime_pow hp, sig_prime_pow hp, geom_sum_succ]

private lemma sig_pos {p : ℕ} (hp : p.Prime) (a : ℕ) : 0 < sig (p ^ a) := by
  rw [sig_prime_pow hp]
  exact sum_pos (fun i _ => pow_pos hp.pos i) ⟨0, by simp⟩

private lemma sig_mod_self {p : ℕ} (hp : p.Prime) (e : ℕ) : sig (p ^ e) % p = 1 % p := by
  induction e with
  | zero => simp [sig]
  | succ e ih => rw [sig_prime_pow_succ hp, Nat.mul_add_mod]

private lemma not_dvd_sig_self {p e : ℕ} (hp : p.Prime) : ¬ p ∣ sig (p ^ e) := by
  intro h
  have h1 := sig_mod_self hp e
  have h2 : sig (p ^ e) % p = 0 := Nat.dvd_iff_mod_eq_zero.mp h
  rw [h2, Nat.mod_eq_of_lt hp.one_lt] at h1
  exact absurd h1.symm one_ne_zero

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

private lemma two_dvd_sig_of_odd_exp {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : e % 2 = 1) :
    2 ∣ sig (p ^ e) := by
  have := sig_mod_two hp hp2 e
  omega

private lemma sig_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) : sig (a * b) = sig a * sig b :=
  h.sum_divisors_mul

private lemma sig_geom_nat {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (p - 1) * sig (p ^ a) + 1 = p ^ (a + 1) := by
  obtain ⟨c, rfl⟩ : ∃ c, p = c + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  simp only [Nat.add_sub_cancel]
  induction a with
  | zero => simp [sig]
  | succ a ih =>
      rw [sig_prime_pow_succ hp]
      have h : c * ((c + 1) * sig ((c + 1) ^ a) + 1) + 1
          = (c + 1) * (c * sig ((c + 1) ^ a) + 1) := by ring
      rw [h, ih]
      ring

private lemma lt_sig_prime_pow (hp : p.Prime) {a : ℕ} (ha : 1 ≤ a) : p ^ a < sig (p ^ a) := by
  have hp2 := hp.two_le
  have hpa : 1 < p ^ a := Nat.one_lt_pow (by omega) hp2
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hgeom := sig_geom_nat hp a
  simp only [Nat.add_sub_cancel] at hgeom
  have hsucc : (q + 1) ^ (a + 1) = (q + 1) ^ a * (q + 1) := by ring
  rw [hsucc] at hgeom
  nlinarith [hgeom, hpa, hp2]

private lemma coprime_sig_special (hp : p.Prime) : Nat.Coprime (sig (p ^ k)) (p ^ k) :=
  (((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_sig_self hp)).symm).pow_right k

private lemma sig_special_dvd_two_mul_sq (hp : p.Prime)
    (heq : sig (p ^ k) * sig (m ^ 2) = 2 * (p ^ k * m ^ 2)) :
    sig (p ^ k) ∣ 2 * m ^ 2 := by
  have hdvd : sig (p ^ k) ∣ p ^ k * (2 * m ^ 2) := ⟨sig (m ^ 2), by rw [heq]; ring⟩
  exact (coprime_sig_special hp).dvd_of_dvd_mul_left hdvd

private lemma sig_sq_lt (hp : p.Prime) (hk : 1 ≤ k) (hm : m ≠ 0)
    (heq : sig (p ^ k) * sig (m ^ 2) = 2 * (p ^ k * m ^ 2)) :
    sig (m ^ 2) < 2 * m ^ 2 := by
  have hlt := lt_sig_prime_pow (p := p) hp hk
  have hm2 : 0 < m ^ 2 := pow_pos (Nat.pos_of_ne_zero hm) 2
  have hpk : 0 < p ^ k := pow_pos hp.pos k
  by_contra hcon
  push_neg at hcon
  nlinarith [heq, hlt, hm2, hpk, hcon]

private theorem exists_dris_index (hp : p.Prime) (hp2 : p ≠ 2) (hk : k % 2 = 1) (hm : m ≠ 0)
    (heq : sig (p ^ k) * sig (m ^ 2) = 2 * (p ^ k * m ^ 2)) :
    ∃ s : ℕ, 0 < s ∧ 2 * m ^ 2 = sig (p ^ k) * s ∧ sig (m ^ 2) = p ^ k * s := by
  obtain ⟨a, ha⟩ : (2 : ℕ) ∣ sig (p ^ k) := two_dvd_sig_of_odd_exp hp hp2 hk
  have hspos : 0 < sig (p ^ k) := sig_pos hp k
  have hdvd : sig (p ^ k) ∣ 2 * m ^ 2 := sig_special_dvd_two_mul_sq hp heq
  have ha_dvd : a ∣ m ^ 2 := by
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨c, ?_⟩
    have h2 : 2 * m ^ 2 = 2 * (a * c) := by rw [hc, ha]; ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  obtain ⟨s, hs⟩ := ha_dvd
  have hm2 : 0 < m ^ 2 := pow_pos (Nat.pos_of_ne_zero hm) 2
  have hspos' : 0 < s := by
    rcases Nat.eq_zero_or_pos s with rfl | h
    · rw [hs] at hm2; simp at hm2
    · exact h
  refine ⟨s, hspos', by rw [hs, ha]; ring, ?_⟩
  have key : sig (p ^ k) * sig (m ^ 2) = sig (p ^ k) * (p ^ k * s) := by
    rw [heq, hs, ha]; ring
  exact Nat.eq_of_mul_eq_mul_left hspos key

private theorem special_pow_lt_sq_or_dris_index_one (hp : p.Prime) (hp2 : p ≠ 2) (hk : k % 2 = 1)
    (hk1 : 1 ≤ k) (hm : m ≠ 0)
    (heq : sig (p ^ k) * sig (m ^ 2) = 2 * (p ^ k * m ^ 2)) :
    p ^ k < m ^ 2 ∨ (2 * m ^ 2 = sig (p ^ k) ∧ sig (m ^ 2) = p ^ k) := by
  obtain ⟨s, hspos, hs2, hs1⟩ := exists_dris_index hp hp2 hk hm heq
  by_cases hlt : p ^ k < m ^ 2
  · exact Or.inl hlt
  · push_neg at hlt
    have hdef := sig_sq_lt hp hk1 hm heq
    have h1 : p ^ k * s < p ^ k * 2 := by
      have : p ^ k * s < 2 * m ^ 2 := by rw [← hs1]; exact hdef
      omega
    have hs_one : s = 1 := by
      have := Nat.lt_of_mul_lt_mul_left h1
      omega
    subst hs_one
    exact Or.inr ⟨by simpa using hs2, by simpa using hs1⟩

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

private theorem exists_sq_of_sig_eq_two_mul_sq {p k m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : k % 4 = 1)
    (h : sig (p ^ k) = 2 * m ^ 2) :
    ∃ t z v : ℕ, k + 1 = 2 * t ∧ t % 2 = 1 ∧ p ^ t + 1 = 2 * z ^ 2 ∧ sig (p ^ (t - 1)) = v ^ 2
      ∧ Nat.Coprime v z ∧ m = v * z := by
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
  have hcopvz : Nat.Coprime v z := by
    have h1 : Nat.Coprime (v ^ 2) (z ^ 2) := by
      rw [← hv, ← hz]; exact hcop
    exact (Nat.coprime_pow_right_iff (n := 2) (by norm_num) _ _).mp
      ((Nat.coprime_pow_left_iff (n := 2) (by norm_num) _ _).mp h1)
  have hmvz : m = v * z := by
    have h2 : m ^ 2 = (v * z) ^ 2 := by
      rw [← hkey, hv, hz]; ring
    exact Nat.pow_left_injective (by norm_num) h2
  exact ⟨t, z, v, ht, htodd, by omega, hv, hcopvz, hmvz⟩

private lemma self_le_sig {n : ℕ} (hn : 0 < n) : n ≤ sig n := by
  rw [sig]
  exact Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors_self n hn.ne')

private theorem not_dris_index_one_of_five_le {p k m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : k % 4 = 1)
    (hk5 : 5 ≤ k) (h1 : sig (p ^ k) = 2 * m ^ 2) (h2 : sig (m ^ 2) = p ^ k) : False := by
  obtain ⟨t, z, v, ht, htodd, hz, hv, hcop, hmvz⟩ := exists_sq_of_sig_eq_two_mul_sq hp hp2 hk h1
  have hp3 : 3 ≤ p := by
    have := hp.two_le; omega
  have ht3 : 3 ≤ t := by omega
  -- `σ (m ^ 2) = σ (v ^ 2) * σ (z ^ 2)`
  have hcopsq : Nat.Coprime (v ^ 2) (z ^ 2) := (hcop.pow 2 2)
  have hsplit : sig (v ^ 2) * sig (z ^ 2) = p ^ k := by
    rw [← h2, hmvz, mul_pow, sig_mul_of_coprime hcopsq]
  -- both factors are powers of `p`
  obtain ⟨a, hale, ha⟩ : ∃ a ≤ k, sig (v ^ 2) = p ^ a :=
    (Nat.dvd_prime_pow hp).mp ⟨sig (z ^ 2), hsplit.symm⟩
  obtain ⟨b, hble, hb⟩ : ∃ b ≤ k, sig (z ^ 2) = p ^ b :=
    (Nat.dvd_prime_pow hp).mp ⟨sig (v ^ 2), by rw [← hsplit]; ring⟩
  have hab : a + b = k := by
    have : p ^ (a + b) = p ^ k := by rw [pow_add, ← ha, ← hb, hsplit]
    exact Nat.pow_right_injective hp.two_le this
  -- lower bounds for the two exponents
  have hpt1 : 0 < p ^ (t - 1) := pow_pos hp.pos _
  have hpt : p ^ t = p ^ (t - 1) * p := by
    rw [← pow_succ, show t - 1 + 1 = t by omega]
  have hP1 : 1 < p ^ (t - 1) := by
    have h1 : p ^ 1 ≤ p ^ (t - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_one] at h1
    omega
  have hvsq : p ^ (t - 1) < v ^ 2 := by
    have hgeom := sig_geom_nat hp (t - 1)
    rw [show t - 1 + 1 = t by omega, hv] at hgeom
    by_contra hcon
    push_neg at hcon
    have hq : (p - 1) * v ^ 2 ≤ (p - 1) * p ^ (t - 1) := Nat.mul_le_mul_left _ hcon
    have hexp : (p - 1) * p ^ (t - 1) + p ^ (t - 1) = p ^ (t - 1) * p := by
      have hp1 : (p - 1) + 1 = p := by omega
      calc (p - 1) * p ^ (t - 1) + p ^ (t - 1) = ((p - 1) + 1) * p ^ (t - 1) := by ring
      _ = p * p ^ (t - 1) := by rw [hp1]
      _ = p ^ (t - 1) * p := by ring
    omega
  have hzsq : p ^ (t - 1) < z ^ 2 := by
    have h3C : 3 * p ^ (t - 1) ≤ p ^ (t - 1) * p := by
      calc 3 * p ^ (t - 1) = p ^ (t - 1) * 3 := by ring
      _ ≤ p ^ (t - 1) * p := Nat.mul_le_mul_left _ hp3
    omega
  have hta : t ≤ a := by
    have hlt : p ^ (t - 1) < p ^ a := by
      calc p ^ (t - 1) < v ^ 2 := hvsq
      _ ≤ sig (v ^ 2) := self_le_sig (by omega)
      _ = p ^ a := ha
    have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
    omega
  have htb : t ≤ b := by
    have hlt : p ^ (t - 1) < p ^ b := by
      calc p ^ (t - 1) < z ^ 2 := hzsq
      _ ≤ sig (z ^ 2) := self_le_sig (by omega)
      _ = p ^ b := hb
    have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
    omega
  omega

private theorem special_pow_lt_sq_of_five_le {p k m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : k % 4 = 1)
    (hk5 : 5 ≤ k) (hm : m ≠ 0)
    (heq : sig (p ^ k) * sig (m ^ 2) = 2 * (p ^ k * m ^ 2)) :
    p ^ k < m ^ 2 := by
  rcases special_pow_lt_sq_or_dris_index_one hp hp2 (by omega) (by omega) hm heq with hlt | ⟨ha, hb⟩
  · exact hlt
  · exact absurd (not_dris_index_one_of_five_le hp hp2 hk hk5 ha.symm hb) (by simp)

private lemma euler_equation_of_perfect {n p k m : ℕ} (hn : n.Perfect) (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hnpm : n = p ^ k * m ^ 2) :
    sig (p ^ k) * sig (m ^ 2) = 2 * (p ^ k * m ^ 2) := by
  have hcop : Nat.Coprime (p ^ k) (m ^ 2) :=
    Nat.Coprime.pow k 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)
  have hsig : sig n = 2 * n := by
    rw [sig]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hn.2).1 hn
  rw [hnpm, sig_mul_of_coprime hcop] at hsig
  exact hsig

private theorem special_pow_lt_sq_of_odd_perfect {n p k m : ℕ} (hn : n.Perfect) (hodd : Odd n)
    (hp : p.Prime) (hk4 : k % 4 = 1) (hk5 : 5 ≤ k) (hpm : ¬ p ∣ m) (hnpm : n = p ^ k * m ^ 2) :
    p ^ k < m ^ 2 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [hnpm] at hodd
    simp at hodd
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : (2 : ℕ) ∣ n := by
      rw [hnpm]
      exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    rw [Nat.odd_iff] at hodd
    omega
  exact special_pow_lt_sq_of_five_le hp hp2 hk4 hk5 hm0 (euler_equation_of_perfect hn hp hpm hnpm)

/-- **For an odd perfect number in Euler form with special exponent `k ≥ 5`, the special part is
smaller than the square part.** -/
theorem solution (n p k m : ℕ) (hn : Nat.Perfect n) (hodd : Odd n) (hp : p.Prime)
    (hk4 : k % 4 = 1) (hk5 : 5 ≤ k) (hpm : ¬ p ∣ m) (hnpm : n = p ^ k * m ^ 2) :
    p ^ k < m ^ 2 :=
  special_pow_lt_sq_of_odd_perfect hn hodd hp hk4 hk5 hpm hnpm
