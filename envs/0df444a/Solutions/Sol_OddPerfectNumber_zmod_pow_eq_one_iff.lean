-- Prove2me | solution 1 for OddPerfectNumber.zmod_pow_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T10:15:06.842087+00:00
-- url     : https://prove2.me/submissions/cdc52917-9d90-4f30-9582-2d93eb096ab6

import Mathlib

-- STAGED direct proof, verbatim from the accepted DHP toolkit
-- (solution 7809bdb2), republished standalone.
theorem solution {q p n : Nat} (hp : 1 ≤ p) :
    ((p : ZMod q) ^ n = 1) ↔ q ∣ p ^ n - 1 := by
  have hpn : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp
  rw [← Nat.modEq_iff_dvd' hpn]
  constructor
  · intro h
    have : ((p ^ n : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by push_cast; simpa using h
    exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp this).symm
  · intro h
    have : ((p ^ n : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr h.symm
    push_cast at this
    simpa using this
