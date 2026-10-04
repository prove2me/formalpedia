-- Prove2me | solution 1 for OddPerfectNumber.geom_ratio_lower_eleven_ge_two_sharp_v2
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:32:14.137685+00:00
-- url     : https://prove2.me/submissions/853ddbdf-acdb-410f-9f56-5e25f53963c4

import Mathlib.Algebra.Ring.GeomSum

theorem solution (n : Nat) (hn : 2 ≤ n) :
    133 * 11 ^ n ≤ 121 * (∑ i ∈ Finset.range (n + 1), 11 ^ i) := by
  induction n, hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    rw [geom_sum_succ, pow_succ]
    have hi := Nat.mul_le_mul_right 11 ih
    omega

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
