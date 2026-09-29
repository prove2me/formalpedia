-- Prove2me | solution 1 for OddPerfectNumber.order_five_phi5_dvd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T18:34:11.52011+00:00
-- url     : https://prove2.me/submissions/ecf9327f-86b3-479e-a4b5-98c679b1fe73

import Mathlib

theorem solution (p q : Nat)
    (hp : p.Prime)
    (hq : q.Prime)
    (h5 : orderOf (q : ZMod p) = 5) :
    p ∣ q ^ 4 + q ^ 3 + q ^ 2 + q + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpow : (q : ZMod p) ^ 5 = 1 := by
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
  have hid :
      ((q : ZMod p) - 1) *
          ((q : ZMod p) ^ 4 + (q : ZMod p) ^ 3 + (q : ZMod p) ^ 2 + (q : ZMod p) + 1) = 0 := by
    rw [← hfactor, hpow]
    ring
  rcases mul_eq_zero.mp hid with h | h
  · have hq1 : (q : ZMod p) = 1 := sub_eq_zero.mp h
    exact absurd hq1 hqne1
  · have hz : ((q ^ 4 + q ^ 3 + q ^ 2 + q + 1 : Nat) : ZMod p) = 0 := by
      simpa using h
    exact (ZMod.natCast_eq_zero_iff (q ^ 4 + q ^ 3 + q ^ 2 + q + 1) p).mp hz
