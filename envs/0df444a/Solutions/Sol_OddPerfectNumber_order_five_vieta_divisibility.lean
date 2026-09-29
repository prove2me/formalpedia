-- Prove2me | solution 1 for OddPerfectNumber.order_five_vieta_divisibility
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T18:34:19.781852+00:00
-- url     : https://prove2.me/submissions/cd2f702c-04f0-450d-bd35-e39ddb7ab628

import Mathlib

theorem solution (p q k : Nat)
    (hp : p.Prime)
    (hpk : p + 1 = q * k)
    (h5 : orderOf (q : ZMod p) = 5) :
    p ∣ q ^ 2 + q + k ^ 2 + k + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : ((p + 1 : Nat) : ZMod p) = 1 := by
    have hpz : (p : ZMod p) = 0 := ZMod.natCast_self p
    rw [Nat.cast_add, Nat.cast_one, hpz, zero_add]
  have hqk : (q : ZMod p) * (k : ZMod p) = 1 := by
    have h : ((q * k : Nat) : ZMod p) = 1 := by
      rw [← hpk]
      exact hp1
    simpa using h
  have hq0 : (q : ZMod p) ≠ 0 := by
    intro hq
    have h1 : (1 : ZMod p) = 0 := by rw [← hqk, hq]; simp
    exact one_ne_zero h1
  have hq5 : (q : ZMod p) ^ 5 = 1 := by
    simpa [h5] using pow_orderOf_eq_one (q : ZMod p)
  have hqne1 : (q : ZMod p) ≠ 1 := by
    intro h
    have h1 : orderOf (q : ZMod p) = 1 := by
      rw [h]
      exact orderOf_one
    omega
  have hfactor :
      (q : ZMod p) ^ 5 - 1 =
        ((q : ZMod p) - 1) *
          ((q : ZMod p) ^ 4 + (q : ZMod p) ^ 3 + (q : ZMod p) ^ 2 + (q : ZMod p) + 1) := by
    ring
  have hphi0 :
      (q : ZMod p) ^ 4 + (q : ZMod p) ^ 3 + (q : ZMod p) ^ 2 + (q : ZMod p) + 1 = 0 := by
    have hid :
        ((q : ZMod p) - 1) *
            ((q : ZMod p) ^ 4 + (q : ZMod p) ^ 3 + (q : ZMod p) ^ 2 + (q : ZMod p) + 1) = 0 := by
      rw [← hfactor, hq5]
      ring
    rcases mul_eq_zero.mp hid with h | h
    · have hq1 : (q : ZMod p) = 1 := sub_eq_zero.mp h
      exact absurd hq1 hqne1
    · exact h
  have hq2k2 : (q : ZMod p) ^ 2 * (k : ZMod p) ^ 2 = 1 := by
    rw [← mul_pow, hqk]
    simp
  have hq2k : (q : ZMod p) ^ 2 * (k : ZMod p) = (q : ZMod p) := by
    calc (q : ZMod p) ^ 2 * (k : ZMod p)
        = (q : ZMod p) * ((q : ZMod p) * (k : ZMod p)) := by ring
      _ = (q : ZMod p) * 1 := by rw [hqk]
      _ = (q : ZMod p) := by ring
  have hkey :
      (q : ZMod p) ^ 2 *
          ((q : ZMod p) ^ 2 + (q : ZMod p) + (k : ZMod p) ^ 2 + (k : ZMod p) + 1)
        = (q : ZMod p) ^ 4 + (q : ZMod p) ^ 3 + (q : ZMod p) ^ 2 + (q : ZMod p) + 1 := by
    calc (q : ZMod p) ^ 2 *
            ((q : ZMod p) ^ 2 + (q : ZMod p) + (k : ZMod p) ^ 2 + (k : ZMod p) + 1)
        = (q : ZMod p) ^ 2 * (q : ZMod p) ^ 2 + (q : ZMod p) ^ 2 * (q : ZMod p)
            + (q : ZMod p) ^ 2 * (k : ZMod p) ^ 2 + (q : ZMod p) ^ 2 * (k : ZMod p)
            + (q : ZMod p) ^ 2 * 1 := by ring
      _ = (q : ZMod p) ^ 4 + (q : ZMod p) ^ 3 + 1 + (q : ZMod p) + (q : ZMod p) ^ 2 := by
            rw [hq2k2, hq2k]; ring
      _ = (q : ZMod p) ^ 4 + (q : ZMod p) ^ 3 + (q : ZMod p) ^ 2 + (q : ZMod p) + 1 := by
            ring
  have hzero :
      (q : ZMod p) ^ 2 *
          ((q : ZMod p) ^ 2 + (q : ZMod p) + (k : ZMod p) ^ 2 + (k : ZMod p) + 1) = 0 := by
    rw [hkey, hphi0]
  have hq2ne : (q : ZMod p) ^ 2 ≠ 0 := pow_ne_zero 2 hq0
  have hz :
      (q : ZMod p) ^ 2 + (q : ZMod p) + (k : ZMod p) ^ 2 + (k : ZMod p) + 1 = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h hq2ne
    · exact h
  have hz' : ((q ^ 2 + q + k ^ 2 + k + 1 : Nat) : ZMod p) = 0 := by
    simpa using hz
  exact (ZMod.natCast_eq_zero_iff (q ^ 2 + q + k ^ 2 + k + 1) p).mp hz'
