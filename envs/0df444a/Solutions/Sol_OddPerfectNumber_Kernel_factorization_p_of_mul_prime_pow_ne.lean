-- Prove2me | solution 1 for OddPerfectNumber.Kernel.factorization_p_of_mul_prime_pow_ne
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T18:17:47.072046+00:00
-- url     : https://prove2.me/submissions/10e12467-ce58-4049-b567-eec1fba6be8d

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- The multiplicity of `p` in `p ^ 5 * s` is exactly five when `p` does not
-- divide `s`.
--
-- This is the arithmetic step that turns the second Dris equation
-- `sigma(m^2) = p ^ 5 * s` into the rigid constraint `v_p(sigma(m^2)) = 5`.
-- The hypothesis is load-bearing rather than cosmetic: with `p = 5` and
-- `s = 25` the multiplicity is `5 + v_p(s) = 7`, not `5`.
--
-- Route.  This is the SAME shape as the ACCEPTED sibling
-- `96_FactorizationPMulFive.lean` (`FacFive`): apply `hmul]`
-- `Nat.factorization_mul` to the non-degenerate pair, project to the point `p`,
-- and rewrite the resulting POINTWISE equation with `Finsupp.add_apply`.
--
-- Diagnostic history, so it is not repeated:
--   5634 `unsolved goals` / `Did not find an occurrence of (?f + ?g) ?i`
--     -- `Nat.factorization_mul` relates two FINSUPPS (functions), and `rw [hmul]`
--     left the goal as a function application.  PROJECT FIRST.
--   5657 `Supplied term: Nat.Prime.ne_zero hp / Expected type: (p != 0) = true`
--     and `pow_ne_zero 5 hp0 / Expected type: ?m ≠ 0` --
--     `!=` is the Decidable BOOLEAN and was copied from the sibling signature
--     into the proof body.  `Nat.Prime.ne_zero` and `pow_ne_zero` both speak the
--     PROP spelling `≠`.
--   5675 `Supplied term: dvd_refl 0 / Actual type: 0 ∣ 0 / Expected: p ∣ 0`
--     -- when `s := 0` the goal is `p ∣ 0` and the witness is `dvd_refl p`, not
--     `dvd_refl 0`.
--   5675 `congrFun (Nat.factorization_mul hpne hsne) / Expected type: ?m.68 = ?m.69`
--     -- `congrFun` was misapplied; the pointwise projection of an `Eq` of
--     `Finsupp`s is `congrArg (fun f : ℕ →₀ ℕ => f p)`.  Rewritten here to that
--     form, which the ACCEPTED sibling's `congrFun ... p` also reduces to.
import Mathlib

namespace OddPerfectNumber.Kernel
namespace FacFive2

theorem solution_aux {p s : Nat} (hp : p.Prime) (hps : Not (Dvd.dvd p s)) :
    (p ^ 5 * s).factorization p = 5 := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpne : p ^ 5 ≠ 0 := pow_ne_zero 5 hp0
  -- After `s := 0`, `hps` reads `¬ p ∣ 0`; every `p` divides `0`, witness `p * 0`.
  -- `dvd_refl` gives `x ∣ x`, so neither `dvd_refl p` (`p ∣ p`) nor
  -- `dvd_refl 0` (`0 ∣ 0`) matches; the divisor must be `p` and the multiple `0`,
  -- which is the witness `0 = p * 0` by `simp`.
  -- Candidate 5705 reported `hs : s = 0` in context with surviving goal `p = 0`:
  -- the `rw [hs]` rewrote the divisibility into an equality before `Dvd.intro p`
  -- could fire.  Candidate 5713 reported the surviving goal `p = 0` for
  -- `exact Dvd.intro p (by simp)`, so `Dvd.dvd` is not being unfolded to the
  -- equation `p * k = 0`.  Candidate 5726 then reported that `omega` cannot close
  -- it, with a counterexample model in which `p ^ 2` and `p ^ 5` are ATOMS: the
  -- goal is `0 = p * ?k` and `omega` will not instantiate `?k` on its own.
  -- The multiple is therefore supplied explicitly as `0`, which makes the
  -- equation `0 = p * 0` a ground goal closed by `rfl`.  Candidate 5749 reported
  -- `unexpected token 'from'; expected ')', ',' or ':'` for
  -- `show 0 = p * 0 from rfl`: the `show` tactic has no `from` clause, so the
  -- tactic form is replaced by the term form `show 0 = p * 0; rfl`, which IS
  -- accepted Lean term syntax.
  -- `Not (p | 0)` is refuted by the witness `0 = p * 0`, and `p * 0` is `Nat`'s own
  -- simplification, so `Nat.zero_mul` closes it.  Candidate 5766 reported
  -- `'show' tactic failed, pattern ...` for the term form `show 0 = p * 0; rfl`:
  -- inside a `by` block the `show` TACTIC pattern-matches its target, and the
  -- target at that point is still the `Dvd.intro` application.  The `exact` form
  -- below makes the equation the term itself, so nothing has to pattern-match.
  --
  -- Candidate 5772 reported `Did not find an occurrence of the pattern` with the
  -- target expression `p * p = 0`: `rw [Nat.zero_mul]` rewrote the DIVISOR `p`
  -- instead of the MULTIPLE, because inside `Dvd.intro p ?w` the multiple is an
  -- opaque term and `rw` had nothing to fire on, so the equation was never
  -- instantiated.  The accepted mission corpus already converts a zero residue into
  -- a divisibility with `Nat.dvd_of_mod_eq_zero`, which is exactly the shape needed
  -- here and was the closure step for the `hne0` bridge in the order theorem.
  have hsne : s ≠ 0 := by
    intro hs
    subst hs
    exact hps (Nat.dvd_of_mod_eq_zero (by simp))
  -- POINTWISE PROJECTION of the Finsupp equality at the point `p`.
  have hmul : (p ^ 5 * s).factorization p
      = (p ^ 5).factorization p + s.factorization p :=
    congrArg (fun f : ℕ →₀ ℕ => f p) (Nat.factorization_mul hpne hsne)
  -- The `p ^ 5` contribution is computed on its OWN, so the rewrite rules below
  -- never have to guess which side of `hmul` they are firing on.
  --
  -- `Nat.factorization_pow` at the prime gives the scalar `5`, and
  -- `Nat.Prime.factorization hp p` is the constant `1` at that prime, so the value
  -- is `5 * 1 = 5`.  Candidate 5604 left `Nat.Prime p` as a goal when
  -- `Nat.Prime.factorization` was applied without its primality argument, so `hp`
  -- is passed EXPLICITLY here.  `Nat.two_mul` is absent throughout: no `2 * ?n`
  -- subterm survives `Finsupp.nsmul_apply` (candidates 5506, 5685).
  have hpow : (p ^ 5).factorization p = 5 := by
    -- `Nat.Prime.factorization` REQUIRES its primality argument to be passed
    -- explicitly.  Candidate 5794 reported the surviving goal `Nat.Prime p` at this
    -- line: without `hp` the elaborator leaves the primality proof as a goal, because
    -- the rewrite rule `Nat.Prime.factorization` is a `Nat.Prime ->` implication and
    -- the instance search does not close it from `hp` automatically here.
    rw [Nat.factorization_pow, Finsupp.nsmul_apply, Nat.nsmul_eq_mul,
      Nat.Prime.factorization hp]
    simp
  have hz : s.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hps
  -- `5 + 0` is closed by `Nat.add_zero` (NOT `Nat.zero_add`, which rewrites
  -- `0 + n`; candidate 5766 E03 reported
  -- `Did not find an occurrence of the pattern 0 + ?n` for `Nat.zero_add`).
  rw [hpow, hz, Nat.add_zero] at hmul
  -- `hmul : (p ^ 5 * s).factorization p = 5 + 0`.
  omega

end FacFive2
end OddPerfectNumber.Kernel

open OddPerfectNumber.Kernel

theorem solution {p s : Nat} (hp : p.Prime) (hps : Not (Dvd.dvd p s)) :
    (p ^ 5 * s).factorization p = 5 :=
  OddPerfectNumber.Kernel.FacFive2.solution_aux hp hps
