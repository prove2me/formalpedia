-- Prove2me | solution 1 for OddPerfectNumber.geom_sum_dvd_branch_split
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:20:05.323564+00:00
-- url     : https://prove2.me/submissions/13ef5bc0-7951-42ce-b06a-2e259c36f7ae

import Mathlib

theorem solution {p q e : Nat} (hp : p.Prime) (hpq : Not (Dvd.dvd p q))
    (hdvd : Dvd.dvd p (∑ i ∈ Finset.range (2 * e + 1), q ^ i)) :
    ((q : ZMod p) = 1 ∧ Dvd.dvd p (2 * e + 1)) ∨
      ((q : ZMod p) ≠ 1 ∧ 1 < orderOf (q : ZMod p) ∧
        Dvd.dvd (orderOf (q : ZMod p)) (2 * e + 1)) := by
  have hsum : (∑ i ∈ Finset.range (2 * e + 1), (q : ZMod p) ^ i) = 0 := by
    have hcast := (ZMod.natCast_eq_zero_iff (∑ i ∈ Finset.range (2 * e + 1), q ^ i) p).mpr hdvd
    simpa only [Nat.cast_sum, Nat.cast_pow] using hcast
  have hpow : (q : ZMod p) ^ (2 * e + 1) = 1 := by
    have hgeom := geom_sum_mul (q : ZMod p) (2 * e + 1)
    rw [hsum, zero_mul] at hgeom
    exact sub_eq_zero.mp hgeom.symm
  have horder : orderOf (q : ZMod p) ∣ 2 * e + 1 := orderOf_dvd_of_pow_eq_one hpow
  by_cases hqone : (q : ZMod p) = 1
  · left
    refine ⟨hqone, (ZMod.natCast_eq_zero_iff (2 * e + 1) p).mp ?_⟩
    simpa only [hqone, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] using hsum
  · right
    have hpositive : 0 < orderOf (q : ZMod p) := Nat.pos_of_dvd_of_pos horder (by omega)
    have hnotone : orderOf (q : ZMod p) ≠ 1 := by
      intro hone
      exact hqone (orderOf_eq_one_iff.mp hone)
    exact ⟨hqone, by omega, horder⟩
