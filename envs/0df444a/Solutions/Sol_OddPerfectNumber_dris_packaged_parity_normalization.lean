-- Prove2me | solution 1 for OddPerfectNumber.dris_packaged_parity_normalization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T16:59:29.756722+00:00
-- url     : https://prove2.me/submissions/243098f0-44e1-42a9-9d9d-d23654d1823f

import Mathlib

open scoped BigOperators

theorem solution (p k m s t d : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m) (hs_odd : Odd s)
    (hsig : (∑ d ∈ (p ^ k).divisors, d) = 2 * t)
    (hdvd : m ^ 2 = t * d)
    (hsigm : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * d)
    (hd_dvd : d ∣ m ^ 2) :
    p % 4 = 1 ∧ k % 4 = 1 := by
  have hm2 : Odd (m ^ 2) := hm.pow
  have ht : Odd t := hm2.of_dvd_nat ⟨d, hdvd⟩
  have hsig4 : (∑ d ∈ (p ^ k).divisors, d) % 4 = 2 := by
    rw [hsig]
    obtain ⟨u, hu⟩ := ht
    omega
  have hpow1 : ∀ i : Nat, p % 4 = 1 → p ^ i % 4 = 1 := by
    intro i hp1
    induction i with
    | zero => simp
    | succ i ih =>
        simp [pow_succ, Nat.mul_mod, hp1, ih]
  have hsum_repr : (∑ d ∈ (p ^ k).divisors, d) =
      ∑ i ∈ Finset.range (k + 1), p ^ i := by
    simpa using (Nat.sum_divisors_prime_pow (f := fun x : Nat => x) hp (k := k))
  have hgeom1 : ∀ n : Nat, p % 4 = 1 →
      (∑ i ∈ Finset.range n, p ^ i) % 4 = n % 4 := by
    intro n hp1
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, Nat.add_mod, hpow1 n hp1, ih]
        omega
  have hpow3 : ∀ i : Nat, p % 4 = 3 →
      p ^ i % 4 = if i % 2 = 0 then 1 else 3 := by
    intro i hp3
    induction i with
    | zero => simp
    | succ i ih =>
        rw [pow_succ, Nat.mul_mod, hp3, ih]
        split_ifs <;> omega
  have hgeom2 : ∀ n : Nat, p % 2 = 1 →
      (∑ i ∈ Finset.range n, p ^ i) % 2 = n % 2 := by
    have hpow2 : ∀ i : Nat, p % 2 = 1 → p ^ i % 2 = 1 := by
      intro i hp1
      induction i with
      | zero => simp
      | succ i ih => simp [pow_succ, Nat.mul_mod, hp1, ih]
    intro n hp1
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, Nat.add_mod]
        rw [hpow2 n hp1, ih]
        omega
  have hgeom3_odd : ∀ v : Nat, p % 4 = 3 →
      (∑ i ∈ Finset.range (2 * v + 2), p ^ i) % 4 = 0 := by
    intro v hp3
    induction v with
    | zero =>
        simp [Finset.sum_range_succ, Nat.add_mod, hp3]
    | succ v ih =>
        have hsq : p ^ 2 % 4 = 1 := by
          rw [show p ^ 2 = p * p by ring, Nat.mul_mod, hp3]
        have hev : p ^ (2 * v + 2) % 4 = 1 := by
          rw [show p ^ (2 * v + 2) = (p ^ 2) ^ (v + 1) by ring,
            Nat.pow_mod, hsq]
          simp
        have hod : p ^ (2 * v + 3) % 4 = 3 := by
          rw [show 2 * v + 3 = 2 * v + 2 + 1 by omega,
            pow_succ, Nat.mul_mod, hev, hp3]
        rw [show 2 * (v + 1) + 2 = 2 * v + 2 + 1 + 1 by omega,
          Finset.sum_range_succ, Finset.sum_range_succ]
        omega
  rcases hp.eq_two_or_odd' with hp_two | hp_odd
  · have hsum_odd : Odd (∑ i ∈ Finset.range (k + 1), 2 ^ i) := by
      have hodd : ∀ n : Nat, Odd (∑ i ∈ Finset.range (n + 1), 2 ^ i) := by
        intro n
        induction n with
        | zero => norm_num
        | succ n ih =>
            rw [show Nat.succ n + 1 = (n + 1) + 1 by omega,
              Finset.sum_range_succ]
            exact ih.add_even ((even_two_mul 1).pow_of_ne_zero (by omega))
      exact hodd k
    have hsum_even : Even (∑ d ∈ (p ^ k).divisors, d) := by
      rw [hsig]
      exact even_two_mul t
    have hsum_even_geo : Even (∑ i ∈ Finset.range (k + 1), 2 ^ i) := by
      have hsum_repr2 : (∑ d ∈ (p ^ k).divisors, d) =
          ∑ i ∈ Finset.range (k + 1), 2 ^ i := by
        simpa [hp_two] using hsum_repr
      rw [← hsum_repr2]
      rw [hsig]
      exact even_two_mul t
    apply False.elim
    apply (Nat.not_even_iff_odd.mpr hsum_odd)
    exact hsum_even_geo
  have hpmod : p % 4 = 1 ∨ p % 4 = 3 := by
    obtain ⟨u, hu⟩ := hp_odd
    have hlt := Nat.mod_lt p (by decide : 0 < 4)
    omega
  rcases hpmod with hp1 | hp3
  · have hsum := hgeom1 (k + 1) hp1
    rw [← hsum_repr] at hsum
    have hk : k % 4 = 1 := by
      rw [hsum] at hsig4
      omega
    exact ⟨hp1, hk⟩
  · have hk_cases : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hk_cases with hk_even | hk_odd
    · have hp2 : p % 2 = 1 := by
        obtain ⟨u, hu⟩ := hp_odd
        omega
      have hsum2 := hgeom2 (k + 1) hp2
      rw [← hsum_repr] at hsum2
      have : (∑ d ∈ (p ^ k).divisors, d) % 2 = 1 := by
        rw [hsum2]
        omega
      rw [hsig] at this
      omega
    · obtain ⟨v, hv⟩ := (Nat.odd_iff).mpr hk_odd
      have hsum3 := hgeom3_odd v hp3
      have hsum_repr3 : (∑ d ∈ (p ^ k).divisors, d) =
          ∑ i ∈ Finset.range (2 * v + 2), p ^ i := by
        calc
          _ = ∑ i ∈ Finset.range (k + 1), p ^ i := hsum_repr
          _ = _ := by rw [hv]
      rw [← hsum_repr3] at hsum3
      rw [hsum3] at hsig4
      omega
