-- Prove2me | solution 1 for OddPerfectNumber.not_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-07T21:19:18.129831+00:00
-- url     : https://prove2.me/submissions/735e20e1-7e10-478f-857d-7418c0b7cc0b

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.Order.Ring.Abs

/-
Prove2Me target c9140301-35c0-4f34-9e0d-afb59c8a7a33,
OddPerfectNumber.not_isSquare, Mathlib 0df444a / Lean 4.33.1.

For a square, the prime exponents are even, so the divisor-count product
has only odd factors. Every divisor of an odd number is odd. Thus the
divisor sum of an odd square is odd, contradicting the perfect-number
identity that this sum is twice the number.
-/

theorem solution (n : ℕ) (hn : Nat.Perfect n) (hodd : Odd n) : ¬ IsSquare n := by
  rintro ⟨m, rfl⟩
  have hcard : Odd (m * m).divisors.card := by
    rw [Nat.card_divisors hn.2.ne']
    refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one ?_
    intro p hp
    have hexponent : (m * m).factorization p = 2 * m.factorization p := by
      rw [← pow_two, Nat.factorization_pow]
      simp
    rw [hexponent]
    exact odd_two_mul_add_one _
  have hfilter : (m * m).divisors.filter Odd = (m * m).divisors := by
    apply Finset.filter_eq_self.mpr
    intro d hd
    exact hodd.of_dvd_nat (Nat.mem_divisors.mp hd).1
  have hsum : Odd (∑ d ∈ (m * m).divisors, d) := by
    rw [Finset.odd_sum_iff_odd_card_odd, hfilter]
    exact hcard
  rw [(Nat.perfect_iff_sum_divisors_eq_two_mul hn.2).mp hn] at hsum
  exact (Nat.not_odd_iff_even.mpr (even_two_mul _)) hsum

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
