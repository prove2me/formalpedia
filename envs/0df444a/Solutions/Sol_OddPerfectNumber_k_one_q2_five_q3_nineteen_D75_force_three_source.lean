-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_D75_force_three_source
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T06:56:51.068322+00:00
-- url     : https://prove2.me/submissions/04928192-5427-4ecc-9310-e707b8a7554e

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.GroupTheory.OrderOfElement

private instance : Fact (Nat.Prime 131) := ⟨by decide +kernel⟩

private theorem power_one (q e : Nat)
    (hd : 263 ∣ ∑ i ∈ Finset.range (2 * e + 1), q ^ i) :
    (q : ZMod 263) ^ (2 * e + 1) = 1 := by
  have hz := (ZMod.natCast_eq_zero_iff (∑ i ∈ Finset.range (2 * e + 1), q ^ i) 263).mpr hd
  have hs : (∑ i ∈ Finset.range (2 * e + 1), (q : ZMod 263) ^ i) = 0 := by
    simpa only [Nat.cast_sum, Nat.cast_pow] using hz
  have hg := geom_sum_mul (q : ZMod 263) (2 * e + 1)
  rw [hs, zero_mul] at hg
  exact sub_eq_zero.mp hg.symm

private theorem even_order (x : ZMod 263) (hx : x ^ 262 = 1)
    (hn : x ^ 131 ≠ 1) : Even (orderOf x) := by
  have hd : orderOf x ∣ 2 * 131 := orderOf_dvd_of_pow_eq_one hx
  by_contra h
  have hc : Nat.Coprime (orderOf x) 2 :=
    Nat.coprime_two_right.mpr (Nat.not_even_iff_odd.mp h)
  exact hn (orderOf_dvd_iff_pow_eq_one.mp (hc.dvd_of_dvd_mul_left hd))

private theorem no_source (q e : Nat) (heven : Even (orderOf (q : ZMod 263))) :
    ¬ 263 ∣ ∑ i ∈ Finset.range (2 * e + 1), q ^ i := by
  intro hd
  have hp := power_one q e hd
  have hdiv := orderOf_dvd_of_pow_eq_one hp
  have he := heven.trans_dvd hdiv
  exact (Nat.not_even_iff_odd.mpr ⟨e, by omega⟩) he

theorem solution (sigma a b c e : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), 263 ^ i))
    (hdiv : 263 ∣ sigma) : 130 ≤ 2 * a := by
  have hprime : Nat.Prime 263 := by decide +kernel
  rw [hsigma] at hdiv
  rcases hprime.dvd_mul.mp hdiv with hrest | h263
  · rcases hprime.dvd_mul.mp hrest with hrest | h19
    · rcases hprime.dvd_mul.mp hrest with h3 | h5
      · have ho : orderOf (3 : ZMod 263) = 131 :=
          orderOf_eq_prime (by decide +kernel) (by decide +kernel)
        have hd := orderOf_dvd_of_pow_eq_one (power_one 3 a h3)
        simp only [Nat.cast_ofNat] at hd
        rw [ho] at hd
        have hle := Nat.le_of_dvd (by omega : 0 < 2 * a + 1) hd
        omega
      · exact (no_source 5 b (even_order _ (by decide +kernel) (by decide +kernel)) h5).elim
    · exact (no_source 19 c (even_order _ (by decide +kernel) (by decide +kernel)) h19).elim
  · have hp := power_one 263 e h263
    have hz : (263 : ZMod 263) = 0 := by decide +kernel
    simp only [Nat.cast_ofNat] at hp
    rw [hz, zero_pow (by omega : 2 * e + 1 ≠ 0)] at hp
    exact ((by decide +kernel : (0 : ZMod 263) ≠ 1) hp).elim

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
