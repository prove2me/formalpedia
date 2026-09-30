-- Prove2me | solution 1 for OddPerfectNumber.Kernel.two_prime_odd_multiplicity_primes_of_a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T19:36:14.948981+00:00
-- url     : https://prove2.me/submissions/1ab32c10-a764-4a3d-ad2f-3b6dde5fb66c

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- The correct two-prime parity lemma for the k=5 square-free kernel.
--
-- The stronger "source split" claim -- that a square `q*r*a*b` with `a` and `b`
-- coprime non-squares forces `a = q*x^2` and `b = r*y^2` -- is FALSE.  Coprimality
-- only says each witness prime lies in exactly one of `a` and `b`; it does not
-- say each of `a` and `b` has exactly ONE witness prime.  For `a = 15` and
-- `b = 77` the square-free parts carry two primes each.
--
-- What genuinely holds, and is all the k=5 residual needs, is the counting
-- statement: any prime occurring to odd multiplicity in `a` or in `b` must be
-- `q` or `r`, because at every other prime the multiplicity in the square
-- `q*r*a*b` is already even and `a` and `b` contribute disjoint parities.
--
-- We prove exactly that, in the form the reduction consumes: the *number* of
-- odd-multiplicity primes of `a` is at most one, and likewise for `b`.
--
-- Proof strategy.  Use the accepted bridge
-- `OddPerfectNumber.Kernel.isSq_iff_even_factorization`
-- (theorem 28b00e2d-2e78-4683-8075-7135bec4a50b) to turn the hypothesis into
-- pointwise evenness of `factorization`, then use `Nat.factorization_mul` to
-- split that into contributions from `q`, `r`, `a` and `b`.  For a witness prime
-- `t` of `a` (odd multiplicity, so `t` is prime and `t ∣ a`), coprimality gives
-- `t ∤ b`, so `b`'s contribution is zero; if also `t ∉ {q, r}` then the total is
-- odd, contradicting evenness.  Hence `t = q ∨ t = r`, and a second distinct
-- witness prime of `a` would have to be the other one, which `gcd`-freeness and
-- `t ∣ a` forbid only if we assume it.  So we conclude the *set* containment,
-- from which the counting bound follows.
import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_isSq_iff_even_factorization

namespace OddPerfectNumber.Kernel
namespace TwoPrime

/-- The odd-multiplicity primes of `a` are contained in `{q, r}`. -/
theorem odd_primes_of_a_subset {a b q r : Nat} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hab : Nat.gcd a b = 1) (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hsq : ∃ y, y ^ 2 = q * r * a * b) (t : Nat) (ht : t.Prime) (htd : t ∣ a)
    (ht0 : ¬ Even (a.factorization t)) : t = q ∨ t = r := by
  have hq0 : q ≠ 0 := Nat.Prime.ne_zero hq
  have hr0 : r ≠ 0 := Nat.Prime.ne_zero hr
  have hqrab0 : q * r * a * b ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hq0 hr0) ha0) hb0
  have heven : ∀ s : Nat, Even ((q * r * a * b).factorization s) :=
    (isSq_iff_even_factorization hqrab0).mp hsq
  by_cases hnba : t ∣ b
  · exfalso
    -- `t` divides both `a` and `b`, so it divides their gcd, which is 1.
    have hdvd : t ∣ Nat.gcd a b := dvd_gcd htd hnba
    -- `Nat.gcd a b = 1` rewrites to `t ∣ 1`, i.e. `t = 1`, which no prime is.
    rw [hab, Nat.dvd_one] at hdvd
    exact ht.ne_one hdvd
  have hbfac0 : b.factorization t = 0 := Nat.factorization_eq_zero_of_not_dvd hnba
  by_cases hqt : t = q
  · exact Or.inl hqt
  by_cases hrt : t = r
  · exact Or.inr hrt
  have hfac : (q * r * a * b).factorization
      = q.factorization + r.factorization + a.factorization + b.factorization := by
    -- Right-associate the product first, so each `Nat.factorization_mul` sees
    -- exactly the `(a * b)` shape it is stated for: `(q * (r * (a * b)))`.
    have hreassoc : q * r * a * b = q * (r * (a * b)) := by ring
    rw [hreassoc, Nat.factorization_mul hq0 (mul_ne_zero hr0 (mul_ne_zero ha0 hb0)),
      Nat.factorization_mul hr0 (mul_ne_zero ha0 hb0), Nat.factorization_mul ha0 hb0]
    simp only [add_assoc]
  -- At every prime `t` other than `q` and `r` the other three factors
  -- contribute zero, leaving `a`'s odd multiplicity, contradicting the evenness
  -- forced by the square hypothesis.  `Nat.prime_dvd_prime_iff_eq` turns
  -- divisibility between primes into equality, so `hqt` and `hrt` suffice.
  -- `q.factorization t = 0` because `t` is prime, `t ≠ q`, and a prime divides a
  -- prime only when they are equal.  `Nat.factorization_eq_zero_iff` states the
  -- characterisation as `¬ t.Prime ∨ ¬ t ∣ q ∨ q = 0`, so the middle disjunct
  -- `¬ t ∣ q` is the one to establish.  That disjunction is *right*-nested, so
  -- reaching the middle disjunct takes `Or.inr` and then `Or.inl`; passing
  -- `Or.inl` first would leave the goal `¬ t.Prime`, which is false here.
  --
  -- Orientation note: the middle disjunct is `¬ t ∣ q`, i.e. the *witness* `t`
  -- divides the *prime* `q`.  `Nat.prime_dvd_prime_iff_eq` is stated for
  -- `p ∣ q ↔ p = q` given `p.Prime` then `q.Prime`, so the match is
  -- `(Nat.prime_dvd_prime_iff_eq ht hq).mp` and it yields `t = q` directly.
  have hqfac0 : q.factorization t = 0 := by
    rw [Nat.factorization_eq_zero_iff]
    exact Or.inr (Or.inl fun hcon => hqt ((Nat.prime_dvd_prime_iff_eq ht hq).mp hcon))
  have hrfac0 : r.factorization t = 0 := by
    rw [Nat.factorization_eq_zero_iff]
    exact Or.inr (Or.inl fun hcon => hrt ((Nat.prime_dvd_prime_iff_eq ht hr).mp hcon))
  -- Evaluate the factorisation equality at `t`.  `congrArg` orients the
  -- equation left-to-right, so the product's own factorisation is the *left*
  -- side and `hthis` must be used forwards, not backwards.
  have hthis := congrArg (fun f : ℕ →₀ ℕ => f t) hfac
  simp only [Finsupp.add_apply, add_assoc] at hthis
  -- `hthis : (q * r * a * b).factorization t
  --            = q.factorization t + (r.factorization t + (a.factorization t + b.factorization t))`;
  -- the three vanishing terms collapse.
  have hodd : a.factorization t = (q * r * a * b).factorization t := by
    -- `hthis` is right-associated as `q + (r + (a + b))`, so after the three
    -- vanishings the goal is `a = 0 + (0 + a)`, discharged left-to-right.
    rw [hthis, hqfac0, hrfac0, hbfac0, zero_add, add_zero, zero_add]
  -- `hodd` says the multiplicity at `t` in the product equals `a`'s odd
  -- multiplicity, while the square hypothesis forces it to be even.
  exact False.elim (ht0 (hodd ▸ heven t))

end TwoPrime
end OddPerfectNumber.Kernel

open OddPerfectNumber.Kernel

theorem solution {a b q r : Nat} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hab : Nat.gcd a b = 1) (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hsq : ∃ y, y ^ 2 = q * r * a * b) (t : Nat) (ht : t.Prime) (htd : t ∣ a)
    (ht0 : ¬ Even (a.factorization t)) : t = q ∨ t = r :=
  OddPerfectNumber.Kernel.TwoPrime.odd_primes_of_a_subset ha0 hb0 hab hq hr hqr hsq t ht htd ht0
