-- Prove2me | solution 1 for OddPerfectNumber.k_one_q_dvd_d_of_q_dvd_t
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T18:09:24.477884+00:00
-- url     : https://prove2.me/submissions/6f9e5e24-0bff-4252-a87b-dc4ba4685704

import Mathlib
import Theorems.Thm_OddPerfectNumber_brent_cohen_te_riele_sigma_exp_bound
import Theorems.Thm_OddPerfectNumber_q_dvd_of_factorization_gap

open OddPerfectNumber

theorem solution (p m d q : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hdvd : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hprime : q.Prime) (hqm : q ∣ m) (hqp : q ≠ p) (hqodd : Odd q)
    (hqmem : q ∈ (m ^ 2).primeFactors)
    (hqdvd : p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i)
    (huniq : ∀ y ∈ (m ^ 2).primeFactors,
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization y + 1), y ^ i → y = q)
    (hsq : IsSquare (q : ZMod p))
    (hsqP : IsSquare (p : ZMod q))
    (hqt : q ∣ (p + 1) / 2) :
    q ∣ d := by
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hp4
  have hq2 : q ≠ 2 := by
    intro h
    subst q
    norm_num at hqodd
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hp1 : p + 1 = 2 * ((p + 1) / 2) := by
    obtain ⟨u, hu⟩ := hpodd
    omega
  have ht0 : (p + 1) / 2 ≠ 0 := by
    have htwo : 2 ≤ p := hp.two_le
    omega
  have hm2 : m ^ 2 ≠ 0 := by
    obtain ⟨_, _, hm2⟩ := Nat.mem_primeFactors.mp hqmem
    exact hm2
  have hd0 : d ≠ 0 := by
    intro hd0
    subst d
    have hmzero : m ^ 2 = 0 := by simpa using hdvd
    exact hm2 hmzero
  have hqnotdvd2 : ¬ q ∣ 2 := by
    intro hdiv
    have hle : q ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    have hge : 2 ≤ q := hprime.two_le
    omega
  have h2fac : (2 : Nat).factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hqnotdvd2
  have hptfac : (p + 1).factorization q = ((p + 1) / 2).factorization q := by
    have hfac := Nat.factorization_mul (a := 2) (b := (p + 1) / 2)
      (by norm_num) ht0
    have hpoint := congrArg (fun f : ℕ →₀ ℕ => f q) hfac
    rw [← hp1] at hpoint
    simp only [Finsupp.add_apply] at hpoint
    rw [h2fac, zero_add] at hpoint
    exact hpoint
  have hp1pos : 0 < p + 1 := by omega
  have hqpow : q ^ (((p + 1) / 2).factorization q) ∣ p + 1 := by
    apply (hprime.pow_dvd_iff_le_factorization (by omega)).mpr
    simpa [hptfac]
  have hqpow_exact : ¬ q ^ (((p + 1) / 2).factorization q + 1) ∣ p + 1 := by
    intro hdiv
    have hle := (hprime.pow_dvd_iff_le_factorization (by omega)).mp hdiv
    rw [hptfac] at hle
    omega
  have hrpos : 1 ≤ ((p + 1) / 2).factorization q :=
    hprime.factorization_pos_of_dvd ht0 hqt
  have hbound : 3 * (((p + 1) / 2).factorization q) ≤ (m ^ 2).factorization q :=
    brent_cohen_te_riele_sigma_exp_bound p q
      ((m ^ 2).factorization q) (((p + 1) / 2).factorization q)
      hp hprime hp2 hq2 (Ne.symm hqp) hrpos
      hqpow hqpow_exact hqdvd
  have hstrict : ((p + 1) / 2).factorization q < (m ^ 2).factorization q := by
    omega
  have hA : (m ^ 2).factorization q = (m ^ 2).factorization q := rfl
  have hr : ((p + 1) / 2).factorization q = ((p + 1) / 2).factorization q := rfl
  exact q_dvd_of_factorization_gap q ((p + 1) / 2) d m
      ((m ^ 2).factorization q) (((p + 1) / 2).factorization q)
      hprime hm2 ht0 hd0 hdvd hA hr hstrict
