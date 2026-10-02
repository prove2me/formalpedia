-- Prove2me | solution 1 for OddPerfectNumber.Kernel.geom_sum_dvd_order_dvd_odd_count
-- status  : ACCEPTED   (prove)
-- author  : @He Jiankui
-- created : 2026-10-01T20:24:13.721294+00:00
-- url     : https://prove2.me/submissions/0b6eb40c-c081-4b65-b6f6-0445b79bf8ef

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

open scoped BigOperators

lemma geom_sum_mul_sub_one {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    (∑ i ∈ Finset.range n, x ^ i) * (x - 1) = x ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
    ring

theorem solution {p q e : Nat} (hp : p.Prime)
    (hdvd : Dvd.dvd p (∑ i ∈ Finset.range (2 * e + 1), q ^ i)) :
    Dvd.dvd (orderOf (q : ZMod p)) (2 * e + 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set N := 2 * e + 1
  obtain ⟨k, hk⟩ := hdvd
  have h_sum_nat : ((∑ i ∈ Finset.range N, q ^ i : ℕ) : ZMod p) = 0 := by
    rw [hk]
    push_cast
    rw [ZMod.natCast_self, MulZeroClass.zero_mul]
  have h_sum_zmod : (∑ i ∈ Finset.range N, (q : ZMod p) ^ i) = 0 := by
    push_cast at h_sum_nat
    exact h_sum_nat
  have h_geom := geom_sum_mul_sub_one (q : ZMod p) N
  have h_sub_zero : (q : ZMod p) ^ N - 1 = 0 := by
    calc (q : ZMod p) ^ N - 1 = (∑ i ∈ Finset.range N, (q : ZMod p) ^ i) * ((q : ZMod p) - 1) := h_geom.symm
    _ = 0 * ((q : ZMod p) - 1) := by rw [h_sum_zmod]
    _ = 0 := zero_mul _
  have h_pow_one : (q : ZMod p) ^ N = 1 := sub_eq_zero.mp h_sub_zero
  exact orderOf_dvd_of_pow_eq_one h_pow_one
