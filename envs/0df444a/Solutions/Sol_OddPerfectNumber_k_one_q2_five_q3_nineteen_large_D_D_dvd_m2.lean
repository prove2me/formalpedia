-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_D_dvd_m2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T17:38:27.371951+00:00
-- url     : https://prove2.me/submissions/ae5b02db-7f76-4ef5-9974-8a77170e45df

import Mathlib

theorem solution (m D p sigma : Nat)
    (hrel : D * sigma = p * m ^ 2)
    (hp : p.Prime)
    (hp_eq : p = 2 * D - 1) :
    D ∣ m ^ 2 := by
  have hcop : Nat.Coprime D p := by
    rw [hp_eq]
    have hD : 1 ≤ D := by
      have hp2 : 2 ≤ p := hp.two_le
      omega
    have hleft : Nat.gcd D (2 * D - 1) ∣ D * 2 :=
      dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) 2
    have hright : Nat.gcd D (2 * D - 1) ∣ 2 * D - 1 :=
      Nat.gcd_dvd_right _ _
    have hdiff : Nat.gcd D (2 * D - 1) ∣ D * 2 - (2 * D - 1) :=
      Nat.dvd_sub hleft hright
    have hone : D * 2 - (2 * D - 1) = 1 := by omega
    rw [hone] at hdiff
    exact Nat.dvd_one.mp hdiff
  have hdvd : D ∣ p * m ^ 2 := ⟨sigma, hrel.symm⟩
  exact hcop.dvd_of_dvd_mul_left hdvd
