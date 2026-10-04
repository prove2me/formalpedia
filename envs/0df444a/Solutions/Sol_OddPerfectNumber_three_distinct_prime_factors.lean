-- Prove2me | solution 1 for OddPerfectNumber.three_distinct_prime_factors
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-07T21:19:32.953721+00:00
-- url     : https://prove2.me/submissions/49eb74f4-7c25-46be-86dc-f0a4119d01ad

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/- Existing Prove2Me target fc51728a-a1a9-4560-afc9-f3ee64e76144.
An odd number with at most two distinct prime factors has divisor-sum ratio
strictly below (3/2)*(5/4), and therefore cannot be perfect. -/

private theorem geometric_bound (c p k : ℕ) (hp : c + 1 ≤ p) :
    c * (∑ i ∈ Finset.range (k + 1), p ^ i) < (c + 1) * p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hpw : (c + 1) * p ^ k ≤ p ^ (k + 1) := by
        simpa [pow_succ, mul_comm] using Nat.mul_le_mul_left (p ^ k) hp
      rw [Finset.sum_range_succ]
      calc
        c * ((∑ i ∈ Finset.range (k + 1), p ^ i) + p ^ (k + 1)) =
            c * (∑ i ∈ Finset.range (k + 1), p ^ i) + c * p ^ (k + 1) := by ring
        _ < p ^ (k + 1) + c * p ^ (k + 1) :=
          Nat.add_lt_add_right (ih.trans_le hpw) _
        _ = (c + 1) * p ^ (k + 1) := by ring

private theorem odd_prime_factor_bound {n p : ℕ} (hodd : Odd n)
    (hp : p ∈ n.primeFactors) : 3 ≤ p ∧ p % 2 = 1 := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hne : p ≠ 2 := by
    intro h
    exact hodd.not_two_dvd_nat (h ▸ Nat.dvd_of_mem_primeFactors hp)
  have hge := hprime.two_le
  have hmod := hprime.eq_two_or_odd.resolve_left hne
  exact ⟨by omega, hmod⟩

theorem solution (n : ℕ) (hn : Nat.Perfect n) (hodd : Odd n) :
    3 ≤ n.primeFactors.card := by
  classical
  have hn0 : n ≠ 0 := ne_of_gt hn.2
  have hprod := Nat.prod_primeFactors_pow_factorization hn0
  have hsum :
      (∏ p ∈ n.primeFactors, ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i) =
        2 * n :=
    (Nat.sum_divisors hn0).symm.trans
      ((Nat.perfect_iff_sum_divisors_eq_two_mul hn.2).mp hn)
  by_contra hcard
  have hle : n.primeFactors.card ≤ 2 := by omega
  by_cases hzero : n.primeFactors.card = 0
  · have hempty := Finset.card_eq_zero.mp hzero
    simp only [hempty, Finset.prod_empty] at hprod hsum
    omega
  by_cases hone : n.primeFactors.card = 1
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hone
    have hmem : p ∈ n.primeFactors := by simp [hp]
    have hbound := geometric_bound 2 p (n.factorization p)
      (odd_prime_factor_bound hodd hmem).1
    simp only [hp, Finset.prod_singleton] at hprod hsum
    nlinarith [hn.2]
  have htwo : n.primeFactors.card = 2 := by omega
  obtain ⟨p, q, hpq, hpqset⟩ := Finset.card_eq_two.mp htwo
  have hordered : ∃ p q : ℕ, p < q ∧ n.primeFactors = {p, q} := by
    rcases lt_or_gt_of_ne hpq with hlt | hlt
    · exact ⟨p, q, hlt, hpqset⟩
    · exact ⟨q, p, hlt, by simpa [Finset.pair_comm] using hpqset⟩
  obtain ⟨p, q, hpq, hpqset⟩ := hordered
  have hp : p ∈ n.primeFactors := by simp [hpqset]
  have hq : q ∈ n.primeFactors := by simp [hpqset]
  obtain ⟨hp3, _⟩ := odd_prime_factor_bound hodd hp
  obtain ⟨_, hqodd⟩ := odd_prime_factor_bound hodd hq
  have hq5 : 5 ≤ q := by omega
  have hpbound := geometric_bound 2 p (n.factorization p) hp3
  have hqbound := geometric_bound 4 q (n.factorization q) hq5
  have hppos : 0 < 3 * p ^ n.factorization p := by positivity
  have hmul := lt_of_le_of_lt
    (Nat.mul_le_mul_right
      (4 * (∑ i ∈ Finset.range (n.factorization q + 1), q ^ i)) hpbound.le)
    (Nat.mul_lt_mul_of_pos_left hqbound hppos)
  simp only [hpqset, Finset.prod_pair (ne_of_lt hpq)] at hprod hsum
  nlinarith [hn.2]

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
