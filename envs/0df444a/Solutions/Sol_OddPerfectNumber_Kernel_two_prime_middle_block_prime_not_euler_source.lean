-- Prove2me | solution 1 for OddPerfectNumber.Kernel.two_prime_middle_block_prime_not_euler_source
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T04:10:18.34975+00:00
-- url     : https://prove2.me/submissions/8bf07c16-4c95-4473-9fb0-e71687ae4b72

import Mathlib

theorem solution {p qC : Nat} (hp : p.Prime)
    (hp5 : p % 4 = 1) (hord : Not (Dvd.dvd (orderOf (qC : ZMod p)) ((p - 1) / 4))) :
    Not (Dvd.dvd p (1 + qC + qC ^ 2)) := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  have h0 : ((1 + qC + qC ^ 2 : ℕ) : ZMod p) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; exact hdvd
  push_cast at h0
  have h3 : (qC : ZMod p) ^ 3 = 1 := by
    linear_combination ((qC : ZMod p) - 1) * h0
  have hne : (qC : ZMod p) ≠ 0 := by
    intro h; rw [h] at h3; simp at h3
  have hd3 : orderOf (qC : ZMod p) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rcases (Nat.dvd_prime Nat.prime_three).1 hd3 with h1 | h1
  · rw [h1] at hord; exact hord (one_dvd _)
  · have hp1 : orderOf (qC : ZMod p) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one hne
    rw [h1] at hp1 hord
    apply hord
    omega
