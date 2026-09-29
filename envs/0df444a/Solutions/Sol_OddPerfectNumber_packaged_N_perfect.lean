-- Prove2me | solution 1 for OddPerfectNumber.packaged_N_perfect
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T10:10:27.578988+00:00
-- url     : https://prove2.me/submissions/42222d3b-6017-442e-b6b3-0a2f6d095364

import Mathlib

-- STAGED direct proof: the shared Dris opening, assembled from
-- accepted-source-verbatim steps (five-proof no_solution).
theorem solution (p k m t d : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hsig : (∑ x ∈ (p ^ k).divisors, x) = 2 * t)
    (hdvd : m ^ 2 = t * d)
    (hsigm : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * d) :
    Nat.Perfect (p ^ k * m ^ 2) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : p ≠ 0 := by omega
  obtain ⟨j, hj⟩ := hm
  have hm0 : m ≠ 0 := by
    intro h
    omega
  have hNpos : 0 < p ^ k * m ^ 2 :=
    Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero hp0) k)
      (pow_pos (Nat.pos_of_ne_zero hm0) 2)
  have hcop : Nat.Coprime (p ^ k) (m ^ 2) :=
    Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)
  have hN : (∑ x ∈ (p ^ k * m ^ 2).divisors, x) = 2 * (p ^ k * m ^ 2) := by
    rw [hcop.sum_divisors_mul, hsig, hsigm, hdvd]
    ring
  exact (Nat.perfect_iff_sum_divisors_eq_two_mul hNpos).mpr hN
