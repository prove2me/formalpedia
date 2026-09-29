-- Prove2me | solution 1 for OddPerfectNumber.k_one_diophantine_t_dvd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T06:21:40.035985+00:00
-- url     : https://prove2.me/submissions/b213cf1e-491a-46e5-b46f-3848eb29a105

import Mathlib

theorem solution (p m : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hpm : ¬ p ∣ m) (hm_odd : Odd m)
    (heq : (1 + p) * (∑ d ∈ (m ^ 2).divisors, d) = 2 * (p * m ^ 2)) :
    (p + 1) / 2 ∣ m ^ 2 := by
  -- `p` is odd, so `(p+1)/2` is exact and `1 + p = 2 * ((p+1)/2)`.
  have h1p : 1 + p = 2 * ((p + 1) / 2) := by omega
  -- Divide the bridge equation by 2 to get `t * σ = p * m^2`.
  have htsig : ((p + 1) / 2) * (∑ d ∈ (m ^ 2).divisors, d) = p * m ^ 2 := by
    have h2 : 2 * (((p + 1) / 2) * (∑ d ∈ (m ^ 2).divisors, d))
        = 2 * (p * m ^ 2) := by
      calc 2 * (((p + 1) / 2) * (∑ d ∈ (m ^ 2).divisors, d))
          = (2 * ((p + 1) / 2)) * (∑ d ∈ (m ^ 2).divisors, d) := by ring
        _ = (1 + p) * (∑ d ∈ (m ^ 2).divisors, d) := by rw [← h1p]
        _ = 2 * (p * m ^ 2) := heq
    exact mul_left_cancel₀ (by norm_num) h2
  -- `t` is coprime to `p`: any common divisor divides `t * 2 - p = 1`.
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
  -- From `t * σ = p * m^2`, `t ∣ p * m^2`, hence `t ∣ m^2`.
  have hdvd : ((p + 1) / 2) ∣ p * m ^ 2 := ⟨_, htsig.symm⟩
  exact hcop.dvd_of_dvd_mul_left hdvd
