-- Prove2me | solution 1 for OddPerfectNumber.k_one_diophantine_deficiency_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T06:22:20.699633+00:00
-- url     : https://prove2.me/submissions/fcfdc88f-47c8-46e2-96b9-064cd705f2ba

import Mathlib

theorem solution (p m : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hpm : ¬ p ∣ m) (hm_odd : Odd m)
    (heq : (1 + p) * (∑ d ∈ (m ^ 2).divisors, d) = 2 * (p * m ^ 2)) :
    ∃ d, m ^ 2 = ((p + 1) / 2) * d ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p * d ∧
      2 * m ^ 2 - (∑ d ∈ (m ^ 2).divisors, d) = d := by
  -- Same opening as the `t ∣ m^2` proof: halve the bridge equation and
  -- take `t = (p+1)/2` coprime to `p`.
  have h1p : 1 + p = 2 * ((p + 1) / 2) := by omega
  have htsig : ((p + 1) / 2) * (∑ d ∈ (m ^ 2).divisors, d) = p * m ^ 2 := by
    have h2 : 2 * (((p + 1) / 2) * (∑ d ∈ (m ^ 2).divisors, d))
        = 2 * (p * m ^ 2) := by
      calc 2 * (((p + 1) / 2) * (∑ d ∈ (m ^ 2).divisors, d))
          = (2 * ((p + 1) / 2)) * (∑ d ∈ (m ^ 2).divisors, d) := by ring
        _ = (1 + p) * (∑ d ∈ (m ^ 2).divisors, d) := by rw [← h1p]
        _ = 2 * (p * m ^ 2) := heq
    exact mul_left_cancel₀ (by norm_num) h2
  have hcop : Nat.Coprime ((p + 1) / 2) p := by
    have hleft : Nat.gcd ((p + 1) / 2) p ∣ ((p + 1) / 2) * 2 :=
      dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) 2
    have hright : Nat.gcd ((p + 1) / 2) p ∣ p := Nat.gcd_dvd_right _ _
    have hdiff : Nat.gcd ((p + 1) / 2) p ∣ ((p + 1) / 2) * 2 - p :=
      Nat.dvd_sub hleft hright
    have hone : ((p + 1) / 2) * 2 - p = 1 := by omega
    rw [hone] at hdiff
    show Nat.gcd ((p + 1) / 2) p = 1
    exact Nat.dvd_one.mp hdiff
  have hdvd : ((p + 1) / 2) ∣ p * m ^ 2 := ⟨_, htsig.symm⟩
  have htdvd : ((p + 1) / 2) ∣ m ^ 2 := hcop.dvd_of_dvd_mul_left hdvd
  -- The quotient `d = m^2 / t` is the deficiency witness.
  obtain ⟨d, hd⟩ := htdvd
  have ht0 : ((p + 1) / 2) ≠ 0 := by omega
  have hsig : (∑ d ∈ (m ^ 2).divisors, d) = p * d := by
    have hpd : ((p + 1) / 2) * (∑ d ∈ (m ^ 2).divisors, d)
        = ((p + 1) / 2) * (p * d) := by
      calc ((p + 1) / 2) * (∑ d ∈ (m ^ 2).divisors, d)
          = p * m ^ 2 := htsig
        _ = p * (((p + 1) / 2) * d) := by rw [← hd]
        _ = ((p + 1) / 2) * (p * d) := by ring
    exact mul_left_cancel₀ ht0 hpd
  refine ⟨d, hd, hsig, ?_⟩
  -- `2 * m^2 - σ = d` is linear in the atoms once `2 * (t*d) = p*d + d`.
  have h2td : 2 * (((p + 1) / 2) * d) = p * d + d := by
    have hrw : (2 * ((p + 1) / 2)) * d = (1 + p) * d := by rw [← h1p]
    calc 2 * (((p + 1) / 2) * d)
        = (2 * ((p + 1) / 2)) * d := by ring
      _ = (1 + p) * d := hrw
      _ = p * d + d := by ring
  omega
