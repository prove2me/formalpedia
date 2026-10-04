-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_nineteen_q4_127_no_five_three
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:32:13.224251+00:00
-- url     : https://prove2.me/submissions/c9165052-0abb-42a7-8def-951a355d13c7

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.GeomSum

private theorem no_five (q e : ℕ) (hfour : (q : ZMod 5) ^ 4 = 1)
    (hone : (q : ZMod 5) ≠ 1) (hthree : (q : ZMod 5) ^ 3 ≠ 1) :
    ¬ 5 ∣ ∑ i ∈ Finset.range (2 * e + 1), q ^ i := by
  intro hd
  have hz := (ZMod.natCast_eq_zero_iff (∑ i ∈ Finset.range (2 * e + 1), q ^ i) 5).mpr hd
  have hs : (∑ i ∈ Finset.range (2 * e + 1), (q : ZMod 5) ^ i) = 0 := by
    simpa only [Nat.cast_sum, Nat.cast_pow] using hz
  have hp : (q : ZMod 5) ^ (2 * e + 1) = 1 := by
    have hgeom := geom_sum_mul (q : ZMod 5) (2 * e + 1)
    rw [hs, zero_mul] at hgeom
    exact sub_eq_zero.mp hgeom.symm
  have hmod : (q : ZMod 5) ^ (2 * e + 1) = (q : ZMod 5) ^ ((2 * e + 1) % 4) := by
    calc
      (q : ZMod 5) ^ (2 * e + 1) =
          (q : ZMod 5) ^ ((2 * e + 1) % 4 + 4 * ((2 * e + 1) / 4)) :=
        congrArg (fun n : ℕ => (q : ZMod 5) ^ n) (Nat.mod_add_div (2 * e + 1) 4).symm
      _ = (q : ZMod 5) ^ ((2 * e + 1) % 4) := by
        rw [pow_add, pow_mul, hfour, one_pow, mul_one]
  have hr : (2 * e + 1) % 4 = 1 ∨ (2 * e + 1) % 4 = 3 := by omega
  rw [hmod] at hp
  rcases hr with hr | hr
  · rw [hr, pow_one] at hp
    exact hone hp
  · rw [hr] at hp
    exact hthree hp

theorem solution (e : Nat) : ¬ 5 ∣ ∑ i ∈ Finset.range (2 * e + 1), 3 ^ i := by
  exact no_five 3 e (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
