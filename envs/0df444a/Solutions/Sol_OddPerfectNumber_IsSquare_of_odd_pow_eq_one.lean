-- Prove2me | solution 1 for OddPerfectNumber.IsSquare_of_odd_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T10:47:14.405465+00:00
-- url     : https://prove2.me/submissions/d836d856-5280-45d4-a7f1-6adcfa75d26d

import Mathlib

-- STAGED direct proof: write d = 2k+1, exhibit q^(k+1) as the root.
-- Only standard names (obtain on Odd, pow_add/pow_one/mul_one, omega).
theorem solution {p q d : Nat} (hd : Odd d)
    (h : (q : ZMod p) ^ d = 1) : IsSquare (q : ZMod p) := by
  obtain ⟨k, rfl⟩ := hd
  refine ⟨(q : ZMod p) ^ (k + 1), ?_⟩
  have h2 : (k + 1) + (k + 1) = (2 * k + 1) + 1 := by omega
  -- NOTE (remote CE 8c661996): after pow_one the goal is 1 * q, so close
  -- with one_mul, not mul_one (see regression test).
  rw [← pow_add, h2, pow_add, h, pow_one, one_mul]
