-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D31_D37_D45_reduced_absurd
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T10:58:14.715092+00:00
-- url     : https://prove2.me/submissions/02597cdc-30c7-405c-ac0b-bbef108d7fdf

import Mathlib

namespace OPN5bef92e0

theorem geom_pow_mod (r p n : ℕ) (hr : 1 ≤ r) (hp : 1 < p)
    (hdiv : p ∣ ∑ i ∈ Finset.range n, r ^ i) : r ^ n % p = 1 := by
  have h1 : (∑ i ∈ Finset.range n, (r - 1 + 1) ^ i) * (r - 1) + 1 = (r - 1 + 1) ^ n :=
    geom_sum_mul_add (r - 1) n
  rw [Nat.sub_add_cancel hr] at h1
  rw [← h1]
  obtain ⟨k, hk⟩ := hdiv
  rw [hk, Nat.add_mod, mul_assoc, Nat.mul_mod_right, zero_add, Nat.mod_mod,
    Nat.mod_eq_of_lt hp]

theorem pow_mod_red (r p L n : ℕ) (hp : 1 < p) (hL : r ^ L % p = 1) (h : r ^ n % p = 1) :
    r ^ (n % L) % p = 1 := by
  have e : r ^ n = (r ^ L) ^ (n / L) * r ^ (n % L) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  rw [e, Nat.mul_mod, Nat.pow_mod, hL, one_pow, Nat.mod_eq_of_lt hp, one_mul,
    Nat.mod_mod] at h
  exact h

theorem key (r p L n : ℕ) (hr : 1 ≤ r) (hp : 1 < p) (hL0 : 0 < L) (hL : r ^ L % p = 1)
    (hLe : 2 ∣ L) (hn : n % 2 = 1) (hchk : ∀ j < L, j % 2 = 1 → r ^ j % p ≠ 1)
    (hdiv : p ∣ ∑ i ∈ Finset.range n, r ^ i) : False := by
  have h2 := geom_pow_mod r p n hr hp hdiv
  have h3 := pow_mod_red r p L n hp hL h2
  exact hchk (n % L) (Nat.mod_lt _ hL0) (by rw [Nat.mod_mod_of_dvd n hLe]; exact hn) h3

theorem d37_127 (n : ℕ) (hdiv : 73 ∣ ∑ i ∈ Finset.range n, 37 ^ i) :
    127 ∣ ∑ i ∈ Finset.range n, 37 ^ i := by
  have h2 := geom_pow_mod 37 73 n (by norm_num) (by norm_num) hdiv
  have h3 := pow_mod_red 37 73 9 n (by norm_num) (by norm_num) h2
  have hchk : ∀ j < 9, 37 ^ j % 73 = 1 → j = 0 := by decide
  have h9 : n % 9 = 0 := hchk _ (Nat.mod_lt _ (by norm_num)) h3
  have e : n = 9 * (n / 9) := by omega
  have h127 : 37 ^ n % 127 = 1 := by
    rw [e, pow_mul, Nat.pow_mod]
    norm_num
  have h1 : (∑ i ∈ Finset.range n, (36 + 1) ^ i) * 36 + 1 = (36 + 1) ^ n :=
    geom_sum_mul_add 36 n
  norm_num at h1
  rw [← h1] at h127
  have h4 : 127 ∣ (∑ i ∈ Finset.range n, 37 ^ i) * 36 := by omega
  exact (Nat.Coprime.dvd_of_dvd_mul_right (by norm_num) h4)

end OPN5bef92e0

theorem solution (m d D p q4 sigma a b c e : Nat)
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDcases : D = 31 ∨ D = 37 ∨ D = 45)
    (hp_eq : p = 2 * D - 1) (hp : p.Prime) (hp4 : p % 4 = 1) (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x) (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4)
    (hq4prime : q4.Prime) (haEven : Even a) (hbEven : Even b)
    (hcEven : Even c) (heEven : Even e)
    (hD45q4 : D = 45 → q4 = 31 ∨ q4 = 41)
    (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) :
    False := by
  have hpd : p ∣ sigma := ⟨d, hglobal.trans hsig⟩
  have hna : (2*a + 1) % 2 = 1 := by omega
  have hnb : (2*b + 1) % 2 = 1 := by omega
  have hnc : (2*c + 1) % 2 = 1 := by omega
  have hne : (2*e + 1) % 2 = 1 := by omega
  rcases hDcases with rfl | rfl | rfl
  · -- D = 31, p = 61, q4 = 31
    have hp61 : p = 61 := by omega
    subst hp61
    have hq : q4 = 31 := by
      have := hDsupport 31 (by norm_num) dvd_rfl
      omega
    subst hq
    rw [hsigma] at hpd
    have hP : Nat.Prime 61 := by norm_num
    rcases (Nat.Prime.dvd_mul hP).1 hpd with h | h
    · rcases (Nat.Prime.dvd_mul hP).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hP).1 h with h | h
        · exact OPN5bef92e0.key 3 61 10 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) hna (by decide) h
        · exact OPN5bef92e0.key 5 61 30 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) hnb (by decide) h
      · exact OPN5bef92e0.key 29 61 12 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) hnc (by decide) h
    · exact OPN5bef92e0.key 31 61 60 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hne (by decide) h
  · -- D = 37, p = 73, q4 = 37
    have hp73 : p = 73 := by omega
    subst hp73
    have hq : q4 = 37 := by
      have := hDsupport 37 (by norm_num) dvd_rfl
      omega
    subst hq
    have hsig' := hsigma
    rw [hsigma] at hpd
    have hP : Nat.Prime 73 := by norm_num
    rcases (Nat.Prime.dvd_mul hP).1 hpd with h | h
    · rcases (Nat.Prime.dvd_mul hP).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hP).1 h with h | h
        · exact OPN5bef92e0.key 3 73 12 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) hna (by decide) h
        · exact OPN5bef92e0.key 5 73 72 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) hnb (by decide) h
      · exact OPN5bef92e0.key 29 73 72 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) hnc (by decide) h
    · have h127 := OPN5bef92e0.d37_127 _ h
      have hs : 127 ∣ sigma := by
        rw [hsig']
        exact Dvd.dvd.mul_left h127 _
      have hQ : Nat.Prime 127 := by norm_num
      have h2 : 127 ∣ 73 * m ^ 2 := by
        rw [← hrel]
        exact Dvd.dvd.mul_left hs _
      rcases (Nat.Prime.dvd_mul hQ).1 h2 with h3 | h3
      · norm_num at h3
      · have h4 : 127 ∣ m := hQ.dvd_of_dvd_pow h3
        have hmem : 127 ∈ m.primeFactors := Nat.mem_primeFactors.2 ⟨hQ, h4, hm0⟩
        have := hsupport 127 hmem
        omega
  · -- D = 45, p = 89, q4 ∈ {31, 41}
    have hp89 : p = 89 := by omega
    subst hp89
    rw [hsigma] at hpd
    have hP : Nat.Prime 89 := by norm_num
    rcases (Nat.Prime.dvd_mul hP).1 hpd with h | h
    · rcases (Nat.Prime.dvd_mul hP).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hP).1 h with h | h
        · exact OPN5bef92e0.key 3 89 88 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) hna (by decide) h
        · exact OPN5bef92e0.key 5 89 44 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) hnb (by decide) h
      · exact OPN5bef92e0.key 29 89 88 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) hnc (by decide) h
    · rcases hD45q4 rfl with hq | hq <;> subst hq
      · exact OPN5bef92e0.key 31 89 88 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) hne (by decide) h
      · exact OPN5bef92e0.key 41 89 88 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) hne (by decide) h
