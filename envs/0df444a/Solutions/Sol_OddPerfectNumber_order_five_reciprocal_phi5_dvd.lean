-- Prove2me | solution 1 for OddPerfectNumber.order_five_reciprocal_phi5_dvd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T18:34:15.735383+00:00
-- url     : https://prove2.me/submissions/84a70984-65d2-4ffd-b44f-50e725143d03

import Mathlib

theorem solution (p q k : Nat)
    (hp : p.Prime)
    (hpk : p + 1 = q * k)
    (h5 : orderOf (q : ZMod p) = 5) :
    p ∣ k ^ 4 + k ^ 3 + k ^ 2 + k + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : ((p + 1 : Nat) : ZMod p) = 1 := by
    have hpz : (p : ZMod p) = 0 := ZMod.natCast_self p
    rw [Nat.cast_add, Nat.cast_one, hpz, zero_add]
  have hqk : (q : ZMod p) * (k : ZMod p) = 1 := by
    have h : ((q * k : Nat) : ZMod p) = 1 := by
      rw [← hpk]
      exact hp1
    simpa using h
  have hq5 : (q : ZMod p) ^ 5 = 1 := by
    simpa [h5] using pow_orderOf_eq_one (q : ZMod p)
  have hk5 : (k : ZMod p) ^ 5 = 1 := by
    have h : ((q : ZMod p) * (k : ZMod p)) ^ 5 = 1 := by
      rw [hqk]
      simp
    rw [mul_pow, hq5, one_mul] at h
    exact h
  have hkne1 : (k : ZMod p) ≠ 1 := by
    intro hk1
    have hq1 : (q : ZMod p) = 1 := by
      calc (q : ZMod p) = (q : ZMod p) * (k : ZMod p) := by rw [hk1, mul_one]
        _ = 1 := hqk
    have h1 : orderOf (q : ZMod p) = 1 := by
      rw [hq1]
      exact orderOf_one
    omega
  have hfactor :
      (k : ZMod p) ^ 5 - 1 =
        ((k : ZMod p) - 1) *
          ((k : ZMod p) ^ 4 + (k : ZMod p) ^ 3 + (k : ZMod p) ^ 2 + (k : ZMod p) + 1) := by
    ring
  have hid :
      ((k : ZMod p) - 1) *
          ((k : ZMod p) ^ 4 + (k : ZMod p) ^ 3 + (k : ZMod p) ^ 2 + (k : ZMod p) + 1) = 0 := by
    rw [← hfactor, hk5]
    ring
  rcases mul_eq_zero.mp hid with h | h
  · have hk1 : (k : ZMod p) = 1 := sub_eq_zero.mp h
    exact absurd hk1 hkne1
  · have hz : ((k ^ 4 + k ^ 3 + k ^ 2 + k + 1 : Nat) : ZMod p) = 0 := by
      simpa using h
    exact (ZMod.natCast_eq_zero_iff (k ^ 4 + k ^ 3 + k ^ 2 + k + 1) p).mp hz
