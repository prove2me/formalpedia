-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_euler_prime_is_five_mod_forty_eight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T16:01:47.400271+00:00
-- url     : https://prove2.me/submissions/dc58c48a-b8e5-4f52-a472-c8a509adf11a

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- Target: OddPerfectNumber.Kernel.five_euler_prime_is_five_mod_forty_eight
--          0d5a698d-616f-449d-87f5-b9829a782d2c
--
-- If `p % 4 = 1` and `p + 1 = 6 * u ^ 2`, then `p % 48 = 5`.
--
-- MATHEMATICS.  `p = 1 (mod 4)` gives `p + 1 = 2 (mod 4)`.  Since `p + 1 = 6 * u ^ 2`, `u`
-- cannot be even: if `u = 2k` then `6 u^2 = 24 k^2 = 0 (mod 4)`.  So `u = 2k+1` is odd and
-- an odd square is `1 (mod 8)`.  Hence `p + 1 = 6 u^2 = 6 (mod 48)` and `p = 5 (mod 48)`.
--
-- DIAGNOSTIC HISTORY.
-- Candidate 6344 (3 groups): L31 supplied `hne : ¬ Odd u` where `¬ ¬ Even u` was expected;
-- L49 "No goals to be solved" was a cascade; L50 `rw [hshape, hmod48]` found no pattern
-- because `hshape` rewrites `p + 1`, which does not occur in a goal about `p`.
-- Candidate 6375 (3 groups): L46 `rcases` failed with
-- `hne : u = 2 * (u / 2) + 1 -> False is not an inductive datatype`, because `by_contra` on
-- the EXISTENTIAL goal `Odd u` yields `Not (Exists ...)`, which cannot be destructured; L63
-- `rw [hinner, hsq8]` found no pattern because `hinner` had already removed `6 * (2k+1)^2`;
-- L67 was a cascade.
--
-- THE REPAIR replaces every negation-based step with the single splitting lemma
-- `Nat.even_or_odd`, which hands over the witness directly as an inductive `Even` or `Odd`
-- case, and lets `omega` close each congruence on `Nat` remainders.  No `ZMod` cast appears,
-- which is deliberate: candidate 6340's E01 failed on an `omega` goal containing
-- `Omega.bmod_div_term 4 [0, 4, -3] [↑p, ↑p / 4, ↑p / 3]`, a mod-4 division atom.
import Mathlib

namespace OddPerfectNumber
namespace Kernel
namespace Mod48

theorem solution_aux (p u : Nat) (hp4 : p % 4 = 1) (hshape : p + 1 = 6 * u ^ 2) :
    p % 48 = 5 := by
  have hp1 : 1 <= p := by omega
  rcases Nat.even_or_odd u with he | ho
  · -- EVEN is impossible: it would make `6 * u ^ 2` vanish modulo `4`.
    obtain ⟨k, hk⟩ := he
    have hsq : u ^ 2 = 4 * (k * k) := by rw [hk]; ring
    have hmod4 : (p + 1) % 4 = 0 := by rw [hshape, hsq]; omega
    omega
  · -- ODD: an odd square is `1 (mod 8)`.
    obtain ⟨k, hk⟩ := ho
    obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
    have hsq8 : ((2 * k + 1) ^ 2 : Nat) % 8 = 1 := by
      have h : (2 * k + 1) ^ 2 = 8 * j + 1 := by nlinarith [hj]
      omega
    have hmod48 : (6 * u ^ 2) % 48 = 6 := by
      rw [hk]
      have hinner : (6 * ((2 * k + 1) ^ 2 : Nat)) = 48 * ((2 * k + 1) ^ 2 / 8)
          + 6 * ((2 * k + 1) ^ 2) % 8 := by
        have h := Nat.mod_add_div (6 * ((2 * k + 1) ^ 2 : Nat)) 8
        omega
      -- Only `hinner` is rewritten: the residual congruence is left to `omega`, which reads
      -- `hsq8` as the atom `((2k+1)^2) % 8`.  Rewriting `hsq8` as well was candidate 6375's
      -- L63 failure, since `hinner` had already removed the pattern it matched.
      rw [hinner]
      omega
    -- `p + 1 = 6 * u ^ 2` transports the residue onto `p` only through this witness, since
    -- `p + 1` does not occur in the goal `p % 48 = 5`.
    have hone : p = 6 * u ^ 2 - 1 := by omega
    -- DIAGNOSTIC HISTORY.
    -- Candidate 6388 (one group): `rw [hone, hmod48]` reported `6 * u ^ 2` absent from
    -- `(6 * u ^ 2 - 1) % 48 = 5`, because that occurrence sits under a SUBTRACTION.
    -- Candidate 6393 (one group): rewriting `hk` into `hmod48` was not enough -- the reported
    -- target was still `(6 * u ^ 2 - 1) % 48 = 5`, because `hone` was NEVER applied to the
    -- GOAL.  The repair therefore rewrites the goal with `hone` FIRST and then hands the
    -- residue to `omega` from the hypothesis, rather than trying to line the two up with `rw`.
    -- Candidate 6400 (two groups): `have hsplit : (6 * u ^ 2) % 48 = 6 := hmod48` reported a
    -- TYPE MISMATCH, actual `6 * (2 * k + 1) ^ 2 % 48 = 6` against expected
    -- `6 * u ^ 2 % 48 = 6`, because `rw [hk] at hmod48` had ALREADY substituted `u` by
    -- `2 * k + 1` in the hypothesis while the goal and `hone` still speak about `u`.
    --
    -- Candidate 6407 (two groups) shows the transport was then unnecessary in the opposite
    -- direction too.  Its reported contexts already contain BOTH atoms in the exact shapes
    -- needed, namely `hk : u = 2 * k + 1`, `hmod48 : 6 * u ^ 2 % 48 = 6` and
    -- `hone : p = 6 * u ^ 2 - 1`, while `rw [← hk]` and `rw [hmod48u]` each reported a missing
    -- pattern (`2 * k + 1` absent from `6 * u ^ 2 % 48 = 6`, and `6 * u ^ 2 % 48` absent from
    -- `(6 * u ^ 2 - 1) % 48 = 5`).  Both failures were `rw` where the context already matches:
    -- the second one in particular cannot work, because `6 * u ^ 2` occurs in the goal only
    -- UNDER a subtraction, which is the same obstruction reported for candidate 6388.
    --
    -- The repair therefore uses NO rewrite at all on the residue.  `hmod48` already carries the
    -- residue in `u`-form, so handing `hmod48`, `hone` and `hshape` to `omega` as atoms closes
    -- `p % 48 = 5` directly, with the `u`-substitution and the subtraction handled inside the
    -- arithmetic rather than by pattern matching.
    have : p % 48 = 5 := by omega
    exact this

end Mod48
end Kernel
end OddPerfectNumber

open OddPerfectNumber
open OddPerfectNumber.Kernel

theorem solution (p u : Nat) (hp4 : p % 4 = 1) (hshape : p + 1 = 6 * u ^ 2) :
    p % 48 = 5 :=
  OddPerfectNumber.Kernel.Mod48.solution_aux p u hp4 hshape
