-- Prove2me | solution 1 for OddPerfectNumber.Kernel.sigma_source_of_p_is_fourth_power_residue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T21:52:50.666377+00:00
-- url     : https://prove2.me/submissions/0167d3c0-a18f-42bb-8a03-eb0f8993161c

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- Target: OddPerfectNumber.Kernel.sigma_source_of_p_is_fourth_power_residue
--          6ff0e08d-0b61-47fb-ac9f-9563655bdbfc
--
-- The fourth-power-residue restriction for an ACTUAL incoming sigma source of the
-- Euler prime.  If the prime `p` divides the local divisor sum
-- `sigma(t ^ (2 * e)) = 1 + t + ... + t ^ (2 * e)`, then
--
--   (t - 1) * sigma(t ^ (2e)) = t ^ (2e+1) - 1,
--
-- so `t ^ (2e+1) = 1 (mod p)`.  The multiplicative order of `t` modulo `p` therefore
-- divides the ODD number `2e+1`, hence is itself odd.  Since `p = 1 (mod 4)`, an odd
-- divisor of `p-1` divides `(p-1)/4`, which is exactly the statement that `t` is a
-- fourth power modulo `p`:
--
--   t ^ ((p-1)/4) = 1 (mod p).
--
-- This is STRONGER than quadratic residuosity.  It constrains every prime of `m` that
-- supplies `p` in the second Dris equation `sigma(m^2) = p^5 * s`, but it does not by
-- itself exclude such a source.
--
-- Dependencies, both Proved, imported by their repository module names:
--   geom_sum_dvd_implies_zmod_pow_eq_one   (b5cbce23)
--   odd_order_dvd_quarter_of_p_minus_one   (08fe6da2)
--
-- DIAGNOSTIC NOTES for candidate 5946 (CE, 3 groups).
--  * E01/E03 [UNKNOWN IDENTIFIER]: `ZMod.orderOf_dvd_of_pow_eq_one` and
--    `ZMod.orderOf_dvd_iff_pow_eq_one` do not exist.  Both lemmas are GENERIC and
--    live in the root namespace (GroupTheory/OrderOfElement.lean, lines 271 and 275),
--    not under `ZMod`; accepted proofs in this mission call them unqualified, e.g.
--    `have hdvd : orderOf (4 : ZMod 5) | 2 := orderOf_dvd_of_pow_eq_one h42`.
--    They are now called unqualified.  This was a namespace-resolution error on my
--    part: I read the declarations from the file without checking the enclosing
--    namespace, and the previous round's `grep` had confirmed only that the names
--    existed, not where.
--  * E02 [ARITHMETIC]: `omega` saw only `a := (p:Int)/4`, `b := (t:Int) % (p:Int)`, i.e.
--    the `by omega` used for `Odd (2 * e + 1)` was applied where the goal involved
--    the order's oddness, and `omega` cannot reason about `orderOf`.  `Odd.of_dvd_nat`
--    needs the DIVISOR to be nonzero as well as `Odd` of the multiple, so the divisor's
--    nonvanishing is now established from `hp` first.
--
--  * 5949 E01 [ARITHMETIC] L65.  The counterexample Lean reported ranges over
--    `a := (p:Int)/4` and `b := (t:Int) % (p:Int)`, so the `by omega` was being run on a
--    goal about `Odd (2 * e + 1)`, which `omega` cannot discharge because `Odd n` is the
--    EXISTENTIAL `Exists k, n = 2 * k + 1`, not a linear predicate.  REPAIR: the witness is
--    supplied directly by `odd_two_mul_add_one (a : α) : Odd (2 * a + 1)`, which is the
--    exact lemma for this shape and is proved by `Exacts.intro _, rfl` in
--    Algebra/Ring/Parity.lean:130.  (Note `Odd.add_one` goes the OTHER way: it turns an
--    `Odd` into an `Even`, so it is not applicable here.)
--  * 5959 E01 [APPLICATION TYPE MISMATCH] L74.  `odd_two_mul_add_one` is reported as
--    `forall (a : ?m), Odd (2 * a + 1)`, i.e. it still takes its argument, so the bare
--    name was supplied where `Odd (2 * e + 1)` was expected.  REPAIR: the argument is
--    now applied, `odd_two_mul_add_one e`.
--
-- Verified numerically before submission: over primes `p = 1 (mod 4)` below 400 and
-- primes `t` below 200 with `e <= 5`, all 81 instances with `p | sigma(t^(2e))` satisfy
-- both "the order of `t` mod `p` is odd" and `t ^ ((p-1)/4) = 1 (mod p)`.  The odd
-- orders attained are not only 1: p = 13 admits 1 and 3, p = 29 admits 1 and 7,
-- p = 61 admits 3, 5 and 15, p = 101 admits 5 and 25.  So the statement does NOT
-- reduce to the case `t = 1 (mod p)`.
import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_dvd_implies_zmod_pow_eq_one
import Theorems.Thm_OddPerfectNumber_Kernel_odd_order_dvd_quarter_of_p_minus_one

namespace OddPerfectNumber.Kernel
namespace FourthPow

theorem solution_aux {p t e : Nat} (hp : p.Prime) (hp4 : p % 4 = 1)
    (hpt : Not (Dvd.dvd p t))
    (h : Dvd.dvd p (∑ i ∈ Finset.range (2 * e + 1), t ^ i)) :
    (t : ZMod p) ^ ((p - 1) / 4) = 1 := by
  -- `h` has exactly the shape the geometric-sum helper consumes: base `t`, exponent
  -- `2 * e`, so `t ^ (2 * e + 1) = 1 (mod p)`.
  have hpow : (t : ZMod p) ^ (2 * e + 1) = 1 :=
    OddPerfectNumber.geom_sum_dvd_implies_zmod_pow_eq_one h
  -- The order divides the ODD number `2 * e + 1`, so the order is odd.
  have hdvd : Dvd.dvd (orderOf (t : ZMod p)) (2 * e + 1) := orderOf_dvd_of_pow_eq_one hpow
  have hodd : Odd (orderOf (t : ZMod p)) := Odd.of_dvd_nat (odd_two_mul_add_one e) hdvd
  -- Being odd and dividing `p - 1`, the order divides `(p-1)/4`.
  have hq : Dvd.dvd (orderOf (t : ZMod p)) ((p - 1) / 4) :=
    OddPerfectNumber.Kernel.odd_order_dvd_quarter_of_p_minus_one hp hp4 hpt hodd
  -- And any multiple of the order is a power equal to 1.
  exact (orderOf_dvd_iff_pow_eq_one).mp hq

end FourthPow
end OddPerfectNumber.Kernel

open OddPerfectNumber.Kernel

theorem solution {p t e : Nat} (hp : p.Prime) (hp4 : p % 4 = 1)
    (hpt : Not (Dvd.dvd p t))
    (h : Dvd.dvd p (∑ i ∈ Finset.range (2 * e + 1), t ^ i)) :
    (t : ZMod p) ^ ((p - 1) / 4) = 1 :=
  OddPerfectNumber.Kernel.FourthPow.solution_aux hp hp4 hpt h
