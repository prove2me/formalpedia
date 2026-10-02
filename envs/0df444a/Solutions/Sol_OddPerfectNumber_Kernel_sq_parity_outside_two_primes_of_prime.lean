-- Prove2me | solution 1 for OddPerfectNumber.Kernel.sq_parity_outside_two_primes_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T07:04:16.765973+00:00
-- url     : https://prove2.me/submissions/e10d0f6f-d240-4f50-8f5c-2e0a65ef02c5

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- Target: OddPerfectNumber.Kernel.sq_parity_outside_two_primes_of_prime
--          bf06b2fb-6247-4217-867d-3b568bad00c9
--
-- The squareclass lemma behind the two-prime residual: if `X * d1^2 * q * r` is a
-- square then every PRIME other than `q` and `r` occurs in `X` to an EVEN multiplicity.
-- Taking `X = (p^2+p+1) * ((p+1)/2 * (p^2-p+1))` and `l = 3` says the
-- odd-multiplicity prime support of the cyclotomic part is exactly `{q, r}`, which is
-- the input to the 3-adic restriction `five_two_prime_index_not_three_mod_twelve`.
--
-- WHY A CORRECTED TARGET WAS PUBLISHED.  The earlier target cd92ad64
-- (`sq_parity_outside_two_primes`) omits `l.Prime` and is FALSE:
--
--   l = 6, q = 2, r = 3, d1 = 1, X = 6 gives
--     X * d1^2 * (q * r) = 36 = 6 ^ 2,  6 ∤ 2,  6 ∤ 3,
--     yet Even (6.factorization 6) = Even 1 is false.
--
-- A composite `l` can divide `q * r` without being `q` or `r` (`6 | 2 * 3`), so
-- `v_l(q * r) = 1` is odd and the even total no longer forces `v_l(X)` even.  A sweep
-- found 508 falsifying instances, all with composite `l`; with `l.Prime` there were
-- none in 39,930 square instances.  `l.Prime` is used at exactly one place: turning
-- `l | q * r` into `l = q ∨ l = r`.
--
-- DIAGNOSTIC NOTES for candidates 5907, 5922 and 5933.
--  * The published binders are BOOL coercions: `X != 0` is `(X != 0) = true`, not a
--    `Ne` proof.  Convert once with `by simpa using h` and use the `Ne` form.
--  * 5907 E02/E03: `rintro hz` has no binder to introduce on a Bool equality.
--  * 5907 E04: `Nat.factorization_mul hm2 hidx0` wants `?m != 0`, not a Bool eq.
--  * 5907 E06 / 5922 E05: `rcases h with .. at h` and `obtain .. := (by .. : T)` are
--    PARSE errors.  Evenness is closed directly with `two_mul` (`2 * n = n + n`).
--  * 5922 E01: `rw [hy, Nat.factorization_pow, ..]` rewrote the goal with `hy` and
--    then searched for `y ^ 2` in a goal that no longer contained it.  The exponent
--    computation now lives in a separate `have hpow`, and the goal only does
--    `rw [hy]` and then `exact hpow t`.
--  * 5933 E01 is the same `rw` ordering fault, now removed.
--  * 5933 E02: after `Nat.factorization_pow` the exponent is `2 • d1.factorization`,
--    an `nsmul` on a `Finsupp`, so `Finsupp.nsmul_apply` did not fire.  That lemma is
--    for `PreLp`/`NormedAddGroupHom`, NOT for `ℕ →₀ ℕ`.  The `nsmul` is removed
--    instead by reading the exponent off `Nat.factorization_pow` in `Even` form.
--  * 5933 E03: `rw [hidx] at hsplit` supplied an `Even` proof where a rewrite needs an
--    equality.  The evenness of the second summand is now applied as a term.
--  * Recorded project API facts used here: after `congrArg (fun f => f l)` the sum is
--    POINTWISE, so `Pi.add_apply` is the rule and not `Pi.add_apply`; and a
--    pointwise projection must never be given an explicit type annotation.

--  * 5976 E01 [UNCLASSIFIED] L85 `unexpected token '\'`.  The file contained the LITERAL
--    six-character text `\u2200` in a binder position instead of the exists sign: my
--    Python patch had written the escape into the file rather than the character.
--    REPAIR: the escape is replaced by the character, and the artefact is now checked for
--    stray `\u` sequences before every submission (see below).
--  * 5945 E01-E05: the `obtain ⟨k, hk⟩ := (by .. )` CONSTRUCTS had survived the
--    5933 repair -- that edit had only replaced their bodies, so the very syntax Lean
--    rejects as a parse error was still there.  5945 reported it at L70/L71 and
--    L87/L88 as a metavariable `?m` that could not be rewritten or destructured, and
--    as `rcases` failing because `x† : ?m` is not an inductive type.  The previous
--    round's claim that they were 'removed' was wrong.  REPAIR: the proof body now
--    uses only `exact ⟨_, rfl⟩` against a rewritten goal, so no `by`-block is ever
--    used as a term.  `Even n` is closed by `two_mul` (`2 * n = n + n`).
--  * 5945 E03: the `rw [hy, ..]` ordering fault reappeared because the same `obtain
--    block wrapped it; now the goal does `rw [hy, Nat.factorization_pow, two_mul]` in
--    a single rewrite, so the exponent is consumed as part of the same step.
--  * 5945 E06: `Pi.add_apply` did not fire on
--    `(X.factorization + (d1^2 * (q*r)).factorization) l`.
--    REPAIR: the projection is taken with no type annotation and the sum is read with
--    `rw [Pi.add_apply] at hsplit`, exactly as the ACCEPTED proof 121_VpThreeModOneB
--    (line 108) does.  Recorded project fact: a pointwise projection must never be
--    given an explicit type annotation -- candidates 5822 and 5835 reported
--    `Actual type: Nat / Expected type: Nat ->₀ Nat` when one was supplied.
-- PRE-SUBMIT CHECK THAT WOULD HAVE CAUGHT IT: after any scripted edit, assert that the
-- file contains no `\u` escape sequence, and run
--   from prove2me.candidate_lint import _v0_text_guard; _v0_text_guard(src, time.time())
-- which rejects unbalanced delimiters.  A literal `\u` is invisible to both, so the
-- explicit `\\u` check is the one that matters.
import Mathlib

namespace OddPerfectNumber.Kernel
namespace SqParity

theorem solution_aux {X d1 q r l : Nat}
    (hX0 : X != 0) (hd10 : d1 != 0) (hl : l.Prime)
    (hm2 : X * d1 ^ 2 * (q * r) != 0)
    (hsq : ∃ y : Nat, y ^ 2 = X * d1 ^ 2 * (q * r))
    (hlq : Not (Dvd.dvd l q)) (hlr : Not (Dvd.dvd l r)) :
    Even (X.factorization l) := by
  have hX0' : X ≠ 0 := by simpa using hX0
  have hd10' : d1 ≠ 0 := by simpa using hd10
  have hm2' : X * d1 ^ 2 * (q * r) ≠ 0 := by simpa using hm2
  have hqr0 : q * r ≠ 0 := by
    rintro hz
    exact hm2' (by rw [hz, Nat.mul_zero])
  have hd10sq : d1 ^ 2 ≠ 0 := pow_ne_zero 2 hd10'
  have hidx0 : d1 ^ 2 * (q * r) ≠ 0 := mul_ne_zero hd10sq hqr0
  -- Every multiplicity in a square is even.  The exponent of `y ^ 2` is a multiple of
  -- two, so `two_mul` supplies the witness for `Even` directly.
  -- The published hypothesis is `y ^ 2 = X * d1 ^ 2 * (q * r)`, which associates as
  -- `(X * d1 ^ 2) * (q * r)`; every intermediate goal here is stated against
  -- `X * (d1 ^ 2 * (q * r))`.  Candidates 5988 E01/E03 reported `rw` failing to find
  -- `X * d1 ^ 2 * (q * r)` in a goal containing `X * (d1 ^ 2 * (q * r))`, so the two
  -- forms are now reconciled ONCE by `simpa [mul_assoc]` instead of by a `rw` that
  -- searches for a pattern the goal does not literally contain.
  have hsqfac : ∀ t : Nat, Even ((X * (d1 ^ 2 * (q * r))).factorization t) := by
    obtain ⟨y, hy⟩ := hsq
    intro t
    have hy' : y ^ 2 = X * (d1 ^ 2 * (q * r)) := by simpa [mul_assoc] using hy
    -- DIAGNOSTIC 6035 E01: `rw [← hy', Nat.factorization_pow, two_mul]` searched for
    -- `2 * ?n` in a goal reading `Even ((2 • y.factorization) t)`.  The exponent produced by
    -- `Nat.factorization_pow` is an `NSMUL` on a `Finsupp`, so `two_mul` cannot match it.
    -- `Finsupp.nsmul_apply` (the declaration the ACCEPTED proof 03_SquareCancellation uses)
    -- turns the `nsmul` into the product `2 * f t` that `two_mul` needs.
    rw [← hy', Nat.factorization_pow]
    simp only [Finsupp.nsmul_apply, Nat.nsmul_eq_mul]
    rw [two_mul]
    exact ⟨_, rfl⟩
  -- `l` divides neither `q` nor `r`, so a prime `l` dividing `q * r` must be one of them.
  have hlz : (q * r).factorization l = 0 := by
    rw [Nat.factorization_eq_zero_of_not_dvd]
    intro hd
    rcases hl.dvd_mul.mp hd with h | h
    · exact hlq h
    · exact hlr h
  -- The index part `d1^2 * (q * r)` contributes an even multiplicity at `l`.  Each
  -- rewrite is applied to a PLAIN `Nat` value obtained by projecting the `Finsupp`
  -- equality with `congrArg` and then reading it with `Finsupp.add_apply`; no `rw` is
  -- ever asked to look through `.factorization`.  The projection carries NO type
  -- annotation, since candidates 5822/5835 reported `Actual type: Nat /
  -- Expected type: Nat ->₀ Nat` when one was supplied.
  -- DIAGNOSTIC 5988 E02 [REWRITE PATTERN NOT FOUND]: after `Nat.factorization_pow`
  -- the exponent is `2 • d1.factorization`, an `nsmul` on a `Finsupp`, so `rw` could
  -- not find `(?n • ?f) ?x`.  The `nsmul` is now eliminated by the CORRECT
  -- declaration `Finsupp.nsmul_apply`, which does hold for a Nat-valued `Finsupp`: the
  -- whole
  -- index part is read through ONE pointwise projection, and the evenness of the
  -- square factor is supplied as a term from `two_mul`.
  -- DIAGNOSTIC 6094 E01 [UNKNOWN IDENTIFIER `hidxpow`].  `hidxpow` had been introduced
  -- INSIDE the `by` block proving `hidx`, so it was not in scope for the later statement
  -- `hYfac`, which needs the same exponent identity.  It is now proved ONCE, before both
  -- uses, at the top level of the proof.
  --
  -- `Nat.factorization_pow` exposes the `nsmul` `2 • d1.factorization`,
  -- `Finsupp.nsmul_apply` turns it into the product `2 * d1.factorization l` -- the
  -- declaration that holds for a Nat-valued `Finsupp` -- and `two_mul` then gives the
  -- sum of two equal terms that `Even` requires.
  have hidxpow : (d1 ^ 2).factorization l = d1.factorization l + d1.factorization l := by
    rw [Nat.factorization_pow, Finsupp.nsmul_apply, Nat.nsmul_eq_mul, two_mul]
  have hidx : Even ((d1 ^ 2 * (q * r)).factorization l) := by
    -- DIAGNOSTIC 6013 E01/E02: `rw [Nat.factorization_pow, two_mul]` searched for `2 * ?n`
    -- in a goal reading `Even ((2 • y.factorization) l)`: the exponent is an `NSMUL` on a
    -- `Finsupp`, not a product, so `two_mul` can never match.  The correct declaration for
    -- a Nat-valued `Finsupp` is `Finsupp.nsmul_apply` (used by the ACCEPTED proofs
    -- 03_SquareCancellation line 42 and 110_ExponentBalanceA), which turns the `nsmul`
    -- into `2 * f l`; `two_mul` is then applied to that product.
    -- DIAGNOSTIC 6035 E02/E03: `rw [hidxpow, ...]` and `rw [hidx] at hval` supplied an
    -- `Even` PROOF where a rewrite needs an EQUALITY, and Lean rejected both before any
    -- goal was reached.  The evenness is therefore carried as a TERM: the witness of the
    -- square factor is destructured and substituted with `omega`, never passed to `rw`.
    -- DIAGNOSTIC 6072 E01/E02, after 6053.  The previous version simplified `hsum` but
    -- then asked `rw [two_mul]` of the GOAL, which still read
    -- `Even ((d1 ^ 2 * (q * r)).factorization l)` with the exponent untouched: `simp only
    -- ... at hsum` simplifies a HYPOTHESIS, never the goal, so the `nsmul` was still there
    -- and `2 * ?n` had no match.  `cases` then failed on the same untouched goal.
    --
    -- The doubling is now done ON THE GOAL, in the one order that works:
    --   `Nat.factorization_pow` exposes the `nsmul`,
    --   `Finsupp.add_apply`/`simp` expose the pointwise sum,
    --   `Finsupp.nsmul_apply` turns the `nsmul` into `2 * f l`,
    -- and only then does `two_mul` produce `f + f`, which is the `Even` goal.
    have hsum := congrArg (fun f : ℕ →₀ ℕ => f l) (Nat.factorization_mul hd10sq hqr0)
    rw [Finsupp.add_apply] at hsum
    rw [hidxpow, hlz] at hsum
    -- `hsum` now reads `f + f + 0 = f + f`, so the goal follows by rewriting with it.
    exact ⟨_, by omega⟩

  -- Split the product at `l` the same way: project with `congrArg`, then evaluate the
  -- pointwise sum with `Finsupp.add_apply`, which is the declaration that holds.
  -- DIAGNOSTIC 6086 E01 [DEPENDENT ELIMINATION FAILED].  `obtain ⟨a, ha⟩ := hval` asked
  -- Lean to destructure `hval` as an `Exists`, but `hval` is an EQUALITY between two `Nat`
  -- values, so dependent elimination had to solve a `padicValNat` equation and failed at
  -- `Eq.refl`.  The evenness is now obtained by rewriting WITH the equation instead of
  -- destructuring it, which is what an equality supports.
  have hval := congrArg (fun f : ℕ →₀ ℕ => f l) (Nat.factorization_mul hX0' hidx0)
  rw [Finsupp.add_apply] at hval
  have hYfac : (d1 ^ 2 * (q * r)).factorization l
      = d1.factorization l + d1.factorization l + (q * r).factorization l := by
    have h := congrArg (fun f : ℕ →₀ ℕ => f l) (Nat.factorization_mul hd10sq hqr0)
    rw [Finsupp.add_apply, hidxpow, hlz] at h
    omega
  -- DIAGNOSTIC 6094 E02 [ARITHMETIC].  The final `omega` was left with `hval` in a form
  -- whose two sides it could not connect, because `hval` is an equation between sums that
  -- `omega` treats as opaque atoms.  The goal is the parity of `X.factorization l`, and
  -- `hval` says that sum equals it, so the witness is read off directly.
  -- DIAGNOSTIC 6116 E01.  `rw [hgoal, ...]` searched for
  -- `(X * (d1^2 * (q*r))).factorization l` in the GOAL `Even (X.factorization l)`, which
  -- does not contain it: the goal is already the PROJECTED value, so no product is present
  -- to rewrite.  The parity must instead be transported the other way, from the evenness
  -- of the square `X * (d1^2 * (q*r))` down to `X.factorization l`.
  --
  -- The square is even at every prime, and at `l` the square factor contributes an even
  -- multiplicity and `q * r` contributes none, so `X` contributes an even one.
  obtain ⟨y, hy⟩ := hsq
  have hy' : y ^ 2 = X * (d1 ^ 2 * (q * r)) := by simpa [mul_assoc] using hy
  have heven : Even ((X * (d1 ^ 2 * (q * r))).factorization l) := by
    rw [← hy', Nat.factorization_pow, Finsupp.nsmul_apply, Nat.nsmul_eq_mul, two_mul]
    exact ⟨_, rfl⟩
  have hproj := congrArg (fun f : ℕ →₀ ℕ => f l) (Nat.factorization_mul hX0' hidx0)
  rw [Finsupp.add_apply] at hproj
  rw [hYfac, hlz] at hproj
  -- `heven` says `X.factorization l + f + f + 0` is a sum of two equal naturals, so the
  -- first summand is even too.
  obtain ⟨k, hk⟩ := heven
  rw [hproj] at hk
  -- `hk : X.factorization l + (d1.factorization l + d1.factorization l) + 0 = 2 * k`.
  -- The two `d1` summands are equal, so the left-hand side is a double; cancelling them
  -- with `Nat.add_right_cancel` leaves `2 * X.factorization l = 2 * k`.
  have hk' : X.factorization l + d1.factorization l + d1.factorization l = 2 * k := by
    omega
  -- `hk' : X.factorization l + d + d = 2 * k` with `d = d1.factorization l`.
  -- Reassociate to `X.factorization l + (d + d)` and collapse the equal tail.
  -- `hk' : X.factorization l + d + d = 2 * k`.  Subtract `d + d` from both sides by
  -- rewriting it as `2 * d` and factoring out `2`: `X + 2d = 2k` and `2X + 2d = 2X + 2d`,
  -- so `Nat.add_right_cancel` applies with the SAME common tail on both sides.
  -- `hk' : X + d + d = 2 * k` with `d = d1.factorization l`.  Cancel the equal tail and
  -- supply the `Even` witness in the required shape `a = a + a` (NOT `2 * a = 2 * b`, which
  -- is what candidates 6179, 6190 and 6201 each sent and which the goal rejects).
  -- `hk' : X + d + d = 2 * k` with `d = d1.factorization l`.  Reassociate, collapse
  -- `d + d` to `2 * d`, then DOUBLE both sides so that the common tail `2 * d + 2 * d`
  -- can be cancelled with `Nat.add_right_cancel`.  `omega` cannot reassociate a `Nat` sum
  -- (candidate 6208), so every step is explicit.
  -- `hk'' : X + (d + d) = 2 * k` with `d = d1.factorization l`.
  --
  -- REPAIRS FOR CANDIDATES 6179, 6190, 6201, 6208 AND 6220 (2 groups).
  --   E01 (L234)  `congrArg (fun n => n * 2) hk''` produced `X + 2d = 2k + 2d`, but the
  --        actual expected type was `X + 2d = 2k + 2d` while the SUPPLIED type was only
  --        `X + 2d = 2k`, so `congrArg` never applied.  The doubling argument is abandoned.
  --   E02 (L243)  `rw [← h2]` faced `X.factorization l = X.factorization l + X.factorization
  --        l`, which `h2 : X * 2 = 2 * k * 2` cannot rewrite.
  --
  -- The clean route: `hk''` says `X + 2d = 2k`, so `2d ≤ 2k`, hence `d ≤ k`, and `X = 2k - 2d`.
  -- Then `X = (k - d) + (k - d)`, which is exactly `Even X` in the shape `n = r + r` that
  -- the `Even` witness obligation requires.  `omega` supplies the Nat subtraction steps
  -- because `Nat` subtraction with a proved lower bound is a linear fact for `omega`.
  have hk'' : X.factorization l + (d1.factorization l + d1.factorization l) = 2 * k := by
    omega
  -- `Nat.le_of_mul_le_mul_left {a b c} (h : c * a <= c * b) (hc : 0 < c)`
  -- (Init/Data/Nat/Basic.lean:769) -- needs BOTH arguments; candidates 6208 and 6220 each
  -- supplied only the inequality, so the positivity obligation was left open.
  have hdle : d1.factorization l ≤ k := by
    have h2d : 2 * d1.factorization l ≤ 2 * k := by omega
    exact Nat.le_of_mul_le_mul_left h2d (by omega)
  -- `X + 2d = 2k` with `d <= k` gives `X = 2k - 2d = (k - d) + (k - d)`, the `Even` shape.
  have hsub : X.factorization l = (k - d1.factorization l) + (k - d1.factorization l) := by
    have hid : X.factorization l + 2 * d1.factorization l = 2 * k := by omega
    omega
  exact ⟨k - d1.factorization l, hsub⟩

end SqParity
end OddPerfectNumber.Kernel

open OddPerfectNumber.Kernel

theorem solution {X d1 q r l : Nat}
    (hX0 : X != 0) (hd10 : d1 != 0) (hl : l.Prime)
    (hm2 : X * d1 ^ 2 * (q * r) != 0)
    (hsq : ∃ y : Nat, y ^ 2 = X * d1 ^ 2 * (q * r))
    (hlq : Not (Dvd.dvd l q)) (hlr : Not (Dvd.dvd l r)) :
    Even (X.factorization l) :=
  OddPerfectNumber.Kernel.SqParity.solution_aux hX0 hd10 hl hm2 hsq hlq hlr
