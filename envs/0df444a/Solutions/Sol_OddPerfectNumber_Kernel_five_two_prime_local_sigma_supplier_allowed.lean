-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_two_prime_local_sigma_supplier_allowed
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T02:56:49.420468+00:00
-- url     : https://prove2.me/submissions/88bf0a7b-6890-4063-8687-e8111f9839ad

import Mathlib

theorem solution {p m d1 q r : Nat}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hqr : q < r)
    (hm0 : m != 0)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r)))
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r)))
    (t : Nat) (ht : t.Prime) (htd : Dvd.dvd t m)
    (htmem : t ∈ m.primeFactors) :
    forall l : Nat, l.Prime -> Dvd.dvd l (∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d) ->
      (l = p \/ l = q \/ l = r \/ Dvd.dvd l m) := by
  intro l hl hdvd
  have hm : m ≠ 0 := by simpa using hm0
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  have hfac : (m ^ 2).factorization t = 2 * m.factorization t := by
    simp [Nat.factorization_pow]
  have hcop : Nat.Coprime (t ^ (2 * m.factorization t)) (m ^ 2 / t ^ (2 * m.factorization t)) := by
    rw [← hfac]
    exact (Nat.coprime_ordCompl ht hm2).pow_left _
  have hsplit : t ^ (2 * m.factorization t) * (m ^ 2 / t ^ (2 * m.factorization t)) = m ^ 2 := by
    rw [← hfac]
    exact Nat.ordProj_mul_ordCompl_eq_self (m ^ 2) t
  have hsig : (∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d) ∣ ∑ d ∈ (m ^ 2).divisors, d := by
    have e := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop
    rw [hsplit] at e
    simp only [ArithmeticFunction.sigma_one_apply] at e
    rw [e]
    exact dvd_mul_right _ _
  have hl2 : l ∣ p ^ 5 * (d1 ^ 2 * (q * r)) := h2 ▸ dvd_trans hdvd hsig
  rcases (Nat.Prime.dvd_mul hl).1 hl2 with h | h
  · left
    exact (Nat.prime_dvd_prime_iff_eq hl hp).1 (hl.dvd_of_dvd_pow h)
  · rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    · right; right; right
      have hld : l ∣ d1 := hl.dvd_of_dvd_pow h
      have hsq : l ^ 2 ∣ 2 * m ^ 2 := by
        rw [h1]
        exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hld 2) _) _
      by_contra hn
      have hc : Nat.Coprime l m := hl.coprime_iff_not_dvd.2 hn
      have hc2 : Nat.Coprime (l ^ 2) (m ^ 2) := Nat.Coprime.pow 2 2 hc
      have h2d : l ^ 2 ∣ 2 := hc2.dvd_of_dvd_mul_right hsq
      have hle : l ^ 2 ≤ 2 := Nat.le_of_dvd (by norm_num) h2d
      have hl2' : 2 ≤ l := hl.two_le
      nlinarith
    · rcases (Nat.Prime.dvd_mul hl).1 h with h | h
      · right; left
        exact (Nat.prime_dvd_prime_iff_eq hl hq).1 h
      · right; right; left
        exact (Nat.prime_dvd_prime_iff_eq hl hr).1 h
