-- Prove2me | solution 1 for OddPerfectNumber.five_dris_odd_prime_exponent_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T12:22:36.307189+00:00
-- url     : https://prove2.me/submissions/3446caa6-ee15-47d4-92c1-9ca1347b7aad

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- Target: OddPerfectNumber.five_dris_odd_prime_exponent_balance
--          2a40075c-5781-4a52-9a78-d8ae34d6d55b
--
-- Exponent balance for the first k=5 Dris equation.  Route A.
--
-- From `2 m^2 = sigma(p^5) * s`, prime factorisation gives, for every `t` with
-- `t ∣ 2`:
--     v_t(2) + v_t(m^2) = v_t(sigma(p^5)) + v_t(s),
-- and since `t ∤ 2` the leftmost term vanishes while `v_t(m^2) = 2 v_t(m)`, so
-- `2 v_t(m) = v_t(sigma(p^5)) + v_t(s)`.  No primality of `t` is needed: the
-- `Nat.factorization` identities hold for every natural number, `t = 1`
-- included.
--
-- Route A transports the Dris equality to an equality of `ℕ →₀ ℕ` functions and
-- then evaluates at `t`.  The nonzero side conditions are required because
-- `Nat.factorization_mul` is vacuous at zero, and `sigma(p^5) ≠ 0` is DERIVED
-- from `hfirst`: if the divisor sum vanished the product would, but
-- `2 * m^2 ≠ 0` for `m ≠ 0`.
--
-- Every declaration is one already exercised by the accepted
-- `20_UniqueOddMultNonSquare.lean` in this directory.
--
-- The proof sits in a `namespace OddPerfectNumber` block because the static
-- guard rejects a bare `open OddPerfectNumber` when no import defines it (a
-- candidate with only that `open` was refused with `unknown namespace`).
import Mathlib

namespace OddPerfectNumber

theorem solution_aux (p m s t : Nat)
    (hm : m ≠ 0) (hs : s ≠ 0) (ht2 : ¬ t ∣ 2)
    (hfirst :
      2 * m ^ 2 =
        (∑ d ∈ (p ^ 5).divisors, d) * s) :
    2 * m.factorization t =
      (∑ d ∈ (p ^ 5).divisors, d).factorization t + s.factorization t := by
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  have hleft0 : 2 * m ^ 2 ≠ 0 := mul_ne_zero (by norm_num) hm20
  have hright0 : (∑ d ∈ (p ^ 5).divisors, d) * s ≠ 0 := by
    rw [← hfirst]
    exact hleft0
  have ha0 : (∑ d ∈ (p ^ 5).divisors, d) ≠ 0 :=
    (mul_ne_zero_iff.mp hright0).1
  have hfac :
      (2 : Nat).factorization + (m ^ 2).factorization =
        (∑ d ∈ (p ^ 5).divisors, d).factorization + s.factorization := by
    calc
      _ = (2 * m ^ 2).factorization :=
        (Nat.factorization_mul (by norm_num) hm20).symm
      _ = ((∑ d ∈ (p ^ 5).divisors, d) * s).factorization :=
        congrArg Nat.factorization hfirst
      _ = _ := Nat.factorization_mul ha0 hs
  have hpoint := congrArg (fun f : ℕ →₀ ℕ => f t) hfac
  simp only [Finsupp.add_apply] at hpoint
  have h2 : (2 : Nat).factorization t = 0 :=
    Nat.factorization_eq_zero_of_not_dvd ht2
  have hpow : (m ^ 2).factorization t = 2 * m.factorization t := by
    rw [Nat.factorization_pow, Finsupp.nsmul_apply, Nat.nsmul_eq_mul,
      Nat.two_mul]
  simpa only [h2, hpow, zero_add] using hpoint

end OddPerfectNumber

open OddPerfectNumber

theorem solution (p m s t : Nat)
    (hm : m ≠ 0) (hs : s ≠ 0) (ht2 : ¬ t ∣ 2)
    (hfirst :
      2 * m ^ 2 =
        (∑ d ∈ (p ^ 5).divisors, d) * s) :
    2 * m.factorization t =
      (∑ d ∈ (p ^ 5).divisors, d).factorization t + s.factorization t :=
  OddPerfectNumber.solution_aux p m s t hm hs ht2 hfirst
