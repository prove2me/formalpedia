-- Prove2me | solution 1 for OddPerfectNumber.Kernel.dris_five_sigma_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T23:33:34.420486+00:00
-- url     : https://prove2.me/submissions/73b68813-f41f-4284-a295-452919eafb5f

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- Target: OddPerfectNumber.Kernel.dris_five_abundancy_of_square_part
--
-- The two Dris equations at exponent five fix the abundancy of the square part.  Write
-- S = sigma(p^5).  Then
--
--   h1 : 2 m^2 = S s
--   h2 : sigma(m^2) = p^5 s
--   =>   S * sigma(m^2) = S * p^5 * s = p^5 * (S * s) = p^5 * 2 * m^2
--                                             (by h2)      (assoc)   (by h1)
--
-- so dividing by m^2 the abundancy of the square part is forced to be
--
--   I(m^2) = sigma(m^2) / m^2 = 2 p^5 / S.
--
-- The index `s` CANCELS, so this is the only invariant of the pair of equations found
-- so far that involves neither the square factor `d1` nor the two odd-multiplicity
-- primes of the index.  Every other structural restriction in this session -- the
-- 3-adic one (`p = 5 mod 12` when 3 is neither kernel prime), the order-3 exclusion of
-- exponent-one cyclotomic primes, and the fourth-power-residue restriction on a sigma
-- source of `p` -- ultimately constrains the exponents of `d1`, which the first equation
-- leaves completely free.  This identity is therefore the natural next target for an
-- argument that has to bypass the index.
--
-- HONEST SCOPE, AND A CORRECTION WORTH RECORDING.  This is a consequence of the two
-- published Dris equations only.  It is NOT a contradiction of the live leaves, which
-- assume `h1` and `h2` alone and do NOT assume that `m^2 * p^5` is an odd perfect
-- number; comparing this abundancy with the `2 / sigma(p^5)` that perfectness would
-- force would give `p^5 = 1`, but that second expression uses the perfectness hypothesis
-- that the Dris-equation formulation has already factored out.
--
-- An earlier draft of the statement read `2 * sigma(m^2) = m^2 * (p^5 * S)`.  That is
-- FALSE, and a numerical test on the genuine first-equation instance
-- p = 5, m = 651, s = 217 caught it: the two sides are 1356250 and 5173020956250.  The
-- correct identity puts the factor S on the LEFT, as proved above.  The draft was never
-- submitted; it is recorded here so the mistake is not repeated.
import Mathlib

namespace OddPerfectNumber.Kernel
namespace Abund

theorem solution_aux (p m s : Nat)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) :
    (∑ d ∈ (p ^ 5).divisors, d) * (∑ d ∈ (m ^ 2).divisors, d) =
      2 * (p ^ 5 * m ^ 2) := by
  -- DIAGNOSTIC 5985 E01 [REWRITE PATTERN NOT FOUND] L48: the chained
  -- `rw [← Nat.mul_assoc, ← h1]` was asked to find a product of THREE factors in a
  -- goal whose right-hand side read `2 * (p ^ 5 * m ^ 2)`, i.e. `2` TIMES a
  -- two-factor product, so the pattern `?n * ?m * ?k` had no match.  The two Dris
  -- equations are now combined in an explicit `calc` whose middle term is literally
  -- `p ^ 5 * (2 * m ^ 2)`, so each step rewrites a subterm that is present verbatim.
  -- ASSOCIATION, STEP BY STEP.  Candidates 6008 E01/E02 showed that a single
  -- `rw [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_assoc]` cannot do this: `rw` picks the
  -- FIRST match of each lemma in turn and re-runs to a fixed point, so after the first
  -- `Nat.mul_assoc` the goal no longer contains a three-factor product and the second
  -- rewrite has nothing to match.  Each `calc` step below therefore performs EXACTLY ONE
  -- reassociation, written out, so every rewrite has a pattern that is present verbatim.
  -- ASSOCIATION AND COMMUTATION, each in its OWN step.  Candidates 6032 E01/E02 showed
  -- that even a single `Nat.mul_assoc` per step is not enough: `rw [← Nat.mul_assoc]` fires
  -- on the FIRST three-factor product it finds, which in the second step was `s * (S * p^5)`
  -- rather than the intended `(S * p^5) * s`, and the goal then needed `Nat.mul_comm` on a
  -- different pair than the one the next step supplied.  `Nat` arithmetic is not handled by
  -- `omega`, which only reasons about linear constraints and knows nothing of products, so
  -- the products are normalised with `ac_rfl`, which proves any two expressions built from
  -- the same commutative-associative atoms.
  have hS : (∑ d ∈ (p ^ 5).divisors, d) * (∑ d ∈ (m ^ 2).divisors, d) = 2 * (p ^ 5 * m ^ 2) := by
    calc
      (∑ d ∈ (p ^ 5).divisors, d) * (∑ d ∈ (m ^ 2).divisors, d)
          = (∑ d ∈ (p ^ 5).divisors, d) * (p ^ 5 * s) := by rw [h2]
      _ = p ^ 5 * ((∑ d ∈ (p ^ 5).divisors, d) * s) := by ac_rfl
      _ = p ^ 5 * (2 * m ^ 2) := by rw [h1]
      _ = 2 * (p ^ 5 * m ^ 2) := by ac_rfl
  exact hS

end Abund
end OddPerfectNumber.Kernel

open OddPerfectNumber.Kernel

theorem solution (p m s : Nat)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) :
    (∑ d ∈ (p ^ 5).divisors, d) * (∑ d ∈ (m ^ 2).divisors, d) =
      2 * (p ^ 5 * m ^ 2) :=
  OddPerfectNumber.Kernel.Abund.solution_aux p m s h1 h2
