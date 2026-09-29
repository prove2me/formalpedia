-- Prove2me | solution 1 for OddPerfectNumber.geom_sum_dvd_implies_zmod_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T10:51:12.166354+00:00
-- url     : https://prove2.me/submissions/af26fba1-993d-4cad-94aa-d7188b42d4f9

import Mathlib

-- Bridge: p | geom sum -> q^(2e+1) = 1 in ZMod p, via geom_sum_mul.
-- Cast the divisibility to ZMod p (ZMod.natCast_self), push the cast
-- through the sum, then multiply by (q - 1).
theorem solution {p q e : Nat}
    (h : p ∣ ∑ i ∈ Finset.range (2*e+1), q^i) :
    (q : ZMod p)^(2*e+1) = 1 := by
  obtain ⟨c, hc⟩ := h
  have hcast : ((∑ i ∈ Finset.range (2*e+1), q^i : ℕ) : ZMod p) = 0 := by
    rw [hc, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  simp only [Nat.cast_sum, Nat.cast_pow] at hcast
  have hgeom := geom_sum_mul (q : ZMod p) (2*e+1)
  rw [hcast, zero_mul] at hgeom
  exact sub_eq_zero.mp hgeom.symm
