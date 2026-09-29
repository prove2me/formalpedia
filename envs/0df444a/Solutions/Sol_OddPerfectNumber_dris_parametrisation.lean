-- Prove2me | solution 1 for OddPerfectNumber.dris_parametrisation
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-08T21:18:30.512042+00:00
-- url     : https://prove2.me/submissions/eb8fc0c5-1d63-4dbb-bb17-8a117ebc7902

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

/-- **The Dris parametrisation of the Euler equation.** -/
theorem solution (p k m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : k % 2 = 1) (hm : m ≠ 0)
    (heq : (∑ d ∈ (p ^ k).divisors, d) * (∑ d ∈ (m ^ 2).divisors, d) = 2 * (p ^ k * m ^ 2)) :
    ∃ s : ℕ, 0 < s ∧ 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s := by
  rw [show (∑ d ∈ (p ^ k).divisors, d) = sig (p ^ k) from rfl,
    show (∑ d ∈ (m ^ 2).divisors, d) = sig (m ^ 2) from rfl] at heq ⊢
  have hcop : Nat.Coprime (sig (p ^ k)) (p ^ k) :=
    (((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_sig_self hp)).symm).pow_right k
  have hdvd : sig (p ^ k) ∣ 2 * m ^ 2 := by
    have h : sig (p ^ k) ∣ p ^ k * (2 * m ^ 2) := ⟨sig (m ^ 2), by rw [heq]; ring⟩
    exact hcop.dvd_of_dvd_mul_left h
  obtain ⟨a, ha⟩ : (2 : ℕ) ∣ sig (p ^ k) := by
    have := sig_mod_two hp hp2 k
    omega
  have hspos : 0 < sig (p ^ k) := sig_pos hp k
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
