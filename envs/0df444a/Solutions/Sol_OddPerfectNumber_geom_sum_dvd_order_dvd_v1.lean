-- Prove2me | solution 1 for OddPerfectNumber.geom_sum_dvd_order_dvd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T17:06:42.116396+00:00
-- url     : https://prove2.me/submissions/51e3ae2c-bf02-4ed4-96d2-c2a33cdc122b

import Mathlib

theorem solution (b q n : Nat)
    (hq : q.Prime) (hb : 1 ≤ b)
    (hdiv : q ∣ ∑ i ∈ Finset.range (n + 1), b ^ i) :
    orderOf (b : ZMod q) ∣ n + 1 := by
  haveI : NeZero q := ⟨by have := hq.two_le; omega⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hbx : b - 1 + 1 = b := Nat.sub_add_cancel hb
  have hgeom := geom_sum_mul_add (b - 1 : ℕ) (n + 1)
  rw [hbx] at hgeom
  have hS0 : ((∑ i ∈ Finset.range (n + 1), b ^ i : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have hcast : ((∑ i ∈ Finset.range (n + 1), b ^ i : ℕ) : ZMod q)
      = ∑ i ∈ Finset.range (n + 1), (b : ZMod q) ^ i := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_pow]
  have hSx0 : (∑ i ∈ Finset.range (n + 1), (b : ZMod q) ^ i) = 0 := by
    rw [← hcast]
    exact hS0
  have h1 : (((∑ i ∈ Finset.range (n + 1), b ^ i) * (b - 1) + 1 : ℕ) : ZMod q)
      = ((b ^ (n + 1) : ℕ) : ZMod q) :=
    congrArg Nat.cast hgeom
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_one, hcast, hSx0, zero_mul, zero_add,
    Nat.cast_pow] at h1
  exact orderOf_dvd_of_pow_eq_one h1.symm
