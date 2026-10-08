-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_first_block_coprime_to_middle_block
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T09:03:03.54697+00:00
-- url     : https://prove2.me/submissions/d07068a0-55e9-4c24-90ce-c128b5ae68b3

import Mathlib

theorem solution {p q c : Nat}
    (hp : Nat.Prime p) (hq2 : q != 2) (hq : Dvd.dvd q (p + 1))
    (hc : c = p ^ 2 + p + 1) :
    Nat.Coprime q c := by
  obtain ⟨k, hk⟩ := hq
  have h : c = 1 + (p * k) * q := by
    rw [hc]
    have : p ^ 2 + p = p * (p + 1) := by ring
    rw [this, hk]; ring
  rw [h, Nat.coprime_add_mul_right_right]
  exact Nat.coprime_one_right q
