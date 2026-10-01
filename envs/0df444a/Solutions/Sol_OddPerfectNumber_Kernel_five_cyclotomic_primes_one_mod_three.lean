-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_cyclotomic_primes_one_mod_three
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:19:50.93521+00:00
-- url     : https://prove2.me/submissions/81cb4b0b-bb27-43df-b15c-a7ba7f712aae

import Mathlib

theorem solution {p q : Nat} (hp : p.Prime) (hp2 : p != 2)
    (hq : q.Prime) (hq3 : q != 3) (hqd : q ∣ p ^ 2 + p + 1) : q % 3 = 1 := by
  let : Fact q.Prime := ⟨hq⟩
  have hpoly : (p : ZMod q) ^ 2 + p + 1 = 0 := by
    have hcast := (ZMod.natCast_eq_zero_iff (p ^ 2 + p + 1) q).mpr hqd
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using hcast
  have hzero : (p : ZMod q) ≠ 0 := by
    intro heq
    simp [heq] at hpoly
  have hone : (p : ZMod q) ≠ 1 := by
    intro heq
    have hthree : (3 : ZMod q) = 0 := by
      calc
        3 = (p : ZMod q) ^ 2 + p + 1 := by rw [heq]; ring
        _ = 0 := hpoly
    have hdiv : q ∣ 3 := (ZMod.natCast_eq_zero_iff 3 q).mp hthree
    have hqeq : q = 3 := (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdiv |>.resolve_left hq.ne_one
    simpa [hqeq] using hq3
  have hpow : (p : ZMod q) ^ 3 = 1 := by
    linear_combination ((p : ZMod q) - 1) * hpoly
  have horder : orderOf (p : ZMod q) = 3 := orderOf_eq_prime hpow hone
  have hdiv : 3 ∣ q - 1 := by
    rw [← horder]
    exact ZMod.orderOf_dvd_card_sub_one hzero
  have hmod := Nat.mod_eq_zero_of_dvd hdiv
  have hqpos := hq.two_le
  omega
