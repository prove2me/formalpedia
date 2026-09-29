-- Prove2me | solution 1 for OddPerfectNumber.no_dris_two_odd_primes_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T22:08:00.224208+00:00
-- url     : https://prove2.me/submissions/f731ce84-023c-4ff8-8d82-793ae9c7ef41
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_dris_packaged_parity_normalization
import Theorems.Thm_OddPerfectNumber_two_distinct_odd_prime_factors
import Theorems.Thm_OddPerfectNumber_no_dris_thirteen_witnessed_core

open Finset OddPerfectNumber

-- Reduction of the general two-odd-prime residual to the existing
-- witnessed-thirteen residual.  The packaged conjunction itself supplies the
-- sigma parity needed by the proved normalization theorem.
theorem solution (p k m s : Nat)
    (hp : p.Prime) (hk : k ≠ 0) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hk2 : 2 ≤ ((k + 1).primeFactors.erase 2).card)
    (hs2 : 2 ≤ s) (hs_not_even : ¬ Even s) (hs_dvd : s ∣ m ^ 2) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  intro h
  obtain ⟨h1, h2⟩ := h
  have hpackaged :
      2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
        (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s := ⟨h1, h2⟩
  have hprod_even : Even ((∑ d ∈ (p ^ k).divisors, d) * s) := by
    rw [← h1]
    exact even_two_mul (m ^ 2)
  have hsig_even : Even (∑ d ∈ (p ^ k).divisors, d) :=
    (Nat.even_mul.mp hprod_even).resolve_right hs_not_even
  obtain ⟨t, ht⟩ := hsig_even
  have hsig : (∑ d ∈ (p ^ k).divisors, d) = 2 * t := by omega
  have hcancel : 2 * m ^ 2 = 2 * (t * s) := by
    calc
      2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s := h1
      _ = (2 * t) * s := by rw [hsig]
      _ = 2 * (t * s) := by ring
  have hms : m ^ 2 = t * s :=
    mul_left_cancel₀ two_ne_zero hcancel
  have hs_odd : Odd s := Nat.not_even_iff_odd.mp hs_not_even
  have hpar := dris_packaged_parity_normalization
    p k m s t s hp hm hpm hs_odd hsig hms h2 hs_dvd
  have hp2_ne : p ≠ 2 := by
    intro hpeq
    subst p
    norm_num at hpar
  have hp2 : (p != 2) = true := bne_iff_ne.mpr hp2_ne
  obtain ⟨q1, q2, hq1ne, hq1p, hq2p, hq1o, hq2o, hq1d, hq2d⟩ :=
    two_distinct_odd_prime_factors k hk2
  have hq1_ge3 : 3 ≤ q1 := by
    have hq1o' := hq1o
    obtain ⟨a, ha⟩ := hq1o'
    have hq1_two : 2 ≤ q1 := hq1p.two_le
    omega
  have hq2_ge3 : 3 ≤ q2 := by
    have hq2o' := hq2o
    obtain ⟨b, hb⟩ := hq2o'
    have hq2_two : 2 ≤ q2 := hq2p.two_le
    omega
  have hprod_ge15 : 15 ≤ q1 * q2 := by
    by_cases hq1_eq3 : q1 = 3
    · have hq2_ne3 : q2 ≠ 3 := by
        intro hq2_eq3
        apply hq1ne
        omega
      have hq2_ge5 : 5 ≤ q2 := by
        have hq2o' := hq2o
        obtain ⟨b, hb⟩ := hq2o'
        omega
      subst q1
      nlinarith
    · have hq1_ge5 : 5 ≤ q1 := by
        have hq1o' := hq1o
        obtain ⟨a, ha⟩ := hq1o'
        omega
      nlinarith
  have hcop : Nat.Coprime q1 q2 := by
    apply (Nat.Prime.coprime_iff_not_dvd hq1p).mpr
    intro hq1_dvd_q2
    exact hq1ne ((Nat.prime_dvd_prime_iff_eq hq1p hq2p).mp hq1_dvd_q2)
  have hprod_dvd : q1 * q2 ∣ k + 1 :=
    hcop.mul_dvd_of_dvd_of_dvd hq1d hq2d
  have hk13 : 13 ≤ k := by
    by_contra hlt
    have hk_le : k ≤ 12 := by omega
    have hprod_le : q1 * q2 ≤ k + 1 := Nat.le_of_dvd (by omega) hprod_dvd
    have hbound : 15 ≤ k + 1 := le_trans hprod_ge15 hprod_le
    omega
  exact (no_dris_thirteen_witnessed_core p k m s q1 q2 hp hp2 hpar.1 hpar.2
    hk13 hm hpm hs2 hs_not_even hq1ne hq1p hq2p hq1o hq2o hq1d hq2d hs_dvd) hpackaged
