-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_dris_odd_source_is_fourth_power_residue
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T15:09:56.533639+00:00
-- url     : https://prove2.me/submissions/c0f62428-5a6d-402b-951e-122337d50bab

import Mathlib

set_option autoImplicit false

namespace P2M3c72d5d6

/-- sigma(m^2) as a product of local geometric sums. -/
theorem sigma_sq_eq_prod (m : Nat) (hm : m ≠ 0) :
    (∑ d ∈ (m ^ 2).divisors, d) =
      ∏ t ∈ m.primeFactors, ∑ i ∈ Finset.range (2 * m.factorization t + 1), t ^ i := by
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  rw [← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.IsMultiplicative.multiplicative_factorization _
      ArithmeticFunction.isMultiplicative_sigma hm2]
  rw [Nat.factorization_pow, Finsupp.prod]
  have hsupp : (2 • m.factorization).support = m.primeFactors := by
    rw [Finsupp.support_smul_eq (by norm_num), Nat.support_factorization]
  rw [hsupp]
  apply Finset.prod_congr rfl
  intro t ht
  have htp : t.Prime := Nat.prime_of_mem_primeFactors ht
  rw [Finsupp.smul_apply, smul_eq_mul, ArithmeticFunction.sigma_one_apply_prime_pow htp]

theorem geom_ne_zero (t n : Nat) : (∑ i ∈ Finset.range (n + 1), t ^ i) ≠ 0 := by
  rw [Finset.sum_range_succ']
  simp

/-- From `p ∣ 1 + t + ... + t^(n-1)` with `n` odd and `p ≡ 1 mod 4`, `t` is a 4th power residue. -/
theorem fourth_power_of_dvd_geom (p t a : Nat) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hdvd : p ∣ ∑ i ∈ Finset.range (2 * a + 1), t ^ i) :
    (t : ZMod p) ^ ((p - 1) / 4) = 1 := by
  have := Fact.mk hp
  set x : ZMod p := (t : ZMod p) with hx
  have h0 : ((∑ i ∈ Finset.range (2 * a + 1), t ^ i : Nat) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  push_cast at h0
  have hgeom := geom_sum_mul x (2 * a + 1)
  rw [h0, zero_mul] at hgeom
  have hxn : x ^ (2 * a + 1) = 1 := (sub_eq_zero.mp hgeom.symm)
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega)] at hxn
    exact zero_ne_one hxn
  have hferm : x ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx0
  have hg := (pow_gcd_eq_one (a := x)).mpr ⟨hferm, hxn⟩
  have hp1 : p - 1 = 4 * ((p - 1) / 4) := by omega
  have hcop : Nat.Coprime 4 (2 * a + 1) := by
    have h2 : Nat.Coprime 2 (2 * a + 1) := by
      rw [Nat.coprime_two_left]
      exact odd_two_mul_add_one a
    have := Nat.Coprime.pow_left 2 h2
    simpa using this
  rw [hp1, Nat.Coprime.gcd_mul_left_cancel _ hcop] at hg
  obtain ⟨c, hc⟩ := Nat.gcd_dvd_left ((p - 1) / 4) (2 * a + 1)
  rw [hc, pow_mul, hg, one_pow]

end P2M3c72d5d6

theorem solution (p m d1 q r : Nat) (hp : p.Prime)
    (hp2 : p != 2) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : Not (Dvd.dvd p m))
    (hq : q.Prime) (hr : r.Prime) (hqr : q < r)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r)))
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r))) :
    exists t : Nat, t.Prime /\ Dvd.dvd t m /\
      Dvd.dvd p (∑ i ∈ Finset.range (2 * m.factorization t + 1), t ^ i) /\
      Not (Even ((∑ i ∈ Finset.range (2 * m.factorization t + 1), t ^ i).factorization p)) /\
      (t : ZMod p) ^ ((p - 1) / 4) = 1 := by
  set s := d1 ^ 2 * (q * r) with hs
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (Nat.not_odd_zero hm)
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, mul_zero] at h1
    have : m ^ 2 = 0 := by omega
    exact hm0 (pow_eq_zero_iff (by norm_num) |>.mp this)
  have hps : ¬ p ∣ s := by
    intro hd
    have h2m : p ∣ 2 * m ^ 2 := by
      rw [h1]; exact Dvd.dvd.mul_left hd _
    rcases (Nat.Prime.dvd_mul hp).mp h2m with h | h
    · have := Nat.le_of_dvd (by norm_num) h
      have := hp.two_le
      omega
    · exact hpm (hp.dvd_of_dvd_pow h)
  have hv : (∑ d ∈ (m ^ 2).divisors, d).factorization p = 5 := by
    rw [h2, Nat.factorization_mul (pow_ne_zero 5 hp.ne_zero) hs0, Finsupp.add_apply,
      Nat.Prime.factorization_pow hp, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hps]
  rw [P2M3c72d5d6.sigma_sq_eq_prod m hm0, Nat.factorization_prod (fun t _ => by
    have := P2M3c72d5d6.geom_ne_zero t (2 * m.factorization t); exact this), Finsupp.coe_finsetSum,
    Finset.sum_apply] at hv
  by_contra hcon
  push Not at hcon
  have heven : Even (∑ t ∈ m.primeFactors,
      (∑ i ∈ Finset.range (2 * m.factorization t + 1), t ^ i).factorization p) := by
    apply Finset.even_sum
    intro t ht
    have htp : t.Prime := Nat.prime_of_mem_primeFactors ht
    have htm : t ∣ m := Nat.dvd_of_mem_primeFactors ht
    by_contra hodd
    have hpos : 0 < (∑ i ∈ Finset.range (2 * m.factorization t + 1), t ^ i).factorization p := by
      rcases Nat.eq_zero_or_pos ((∑ i ∈ Finset.range (2 * m.factorization t + 1), t ^ i).factorization p) with h | h
      · rw [h] at hodd; exact absurd ⟨0, rfl⟩ hodd
      · exact h
    have hpd : p ∣ ∑ i ∈ Finset.range (2 * m.factorization t + 1), t ^ i :=
      Nat.dvd_of_factorization_pos (Nat.pos_iff_ne_zero.mp hpos)
    exact hcon t htp htm hpd hodd (P2M3c72d5d6.fourth_power_of_dvd_geom p t _ hp hp4 hpd)
  rw [hv] at heven
  exact absurd heven (by decide)
