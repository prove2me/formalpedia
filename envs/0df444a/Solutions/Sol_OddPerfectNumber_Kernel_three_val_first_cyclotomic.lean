-- Prove2me | solution 1 for OddPerfectNumber.Kernel.three_val_first_cyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T09:42:21.933843+00:00
-- url     : https://prove2.me/submissions/bec65d2c-83f6-4f41-9a27-bec3236f4d65

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- Target: OddPerfectNumber.Kernel.three_val_first_cyclotomic
--
-- When `p = 1 (mod 3)` the first cyclotomic block `p^2 + p + 1` is `3 (mod 9)`, hence
-- divisible by `3` but not by `9`.
--
-- REPAIRS FOR CANDIDATES 6136, 6145, 6168, 6175, 6206, 6216, 6225, 6232, 6245 AND 6254.
--
-- 6254 E01 (L42)  `omega` could not prove `(p^2 + p + 1) % 3 = 0` from `h1 : p % 3 = 1`.
--   The goal state named the atoms that defeated it:
--       a := ↑p / 3 ,  b := ↑(p^2) ,  c := ↑(p^2 + p + 1) / 3
--   `omega` splits `%` by introducing the quotient, and `p^2` is a `pow`, not an atom it can
--   linearise, so the constraints never close.  THE FIX IS TO NEVER LET `omega` SEE A `%`
--   OF A `pow`.  The block congruence is therefore built with the `Nat.ModEq` closure, whose
--   `.pow` DOES handle `p^2` (Mathlib/Data/Nat/ModEq.lean:157), and the ONLY `%` equation
--   `omega` ever sees is the final unfolding of that congruence.
--
-- 6254 E02 (L59)  `interval_cases h : p % 9` failed with "could not find upper bound on
--   p % 9": the bound is not automatic.  `interval_cases` needs BOTH a lower and an upper
--   bound available in the context, and the upper bound is `Nat.mod_lt (by omega) 9`.  So the
--   residue is named ONCE, with its bound supplied, and only then split.
--
-- 6245 E01  `h1.pow 2` failed: "Invalid field `pow`: The environment does not contain
--   `Eq.pow`".  `h1` is an `Eq`, and the `pow` FIELD exists only on a `Nat.ModEq` value.
--   Coercing first -- `have hpm3 : p ≡ 1 [MOD 3] := h1` -- is a definitional unfolding and
--   makes the field legal.  That is the shape used below.
--
-- 6245/6232 E01  `Nat.mul_mod` matches `a * b % n`, NOT `a ^ k % n`, so it cannot reduce
--   `p^2 % 3`; that was the original cause of the 6232 `?a * ?b % ?n` failure.
import Mathlib

namespace OddPerfectNumber
namespace Kernel
namespace Three

theorem solution {p : Nat} (hp4 : 4 <= p) (h1 : p % 3 = 1) :
    (3 : Nat) ∣ p ^ 2 + p + 1 ∧ ¬ (9 : Nat) ∣ p ^ 2 + p + 1 := by
  -- MOD 3.  `hpm3 : p ≡ 1 [MOD 3]` is `h1` unfolded (`Nat.ModEq` IS `% =`); `.pow` is then
  -- legal on it and handles the `p^2` term, which no `%`-rewrite could.
  have hpm3 : p ≡ (1 : Nat) [MOD 3] := h1
  have hsum3 : p ^ 2 + p + 1 ≡ (1 + 1 + 1 : Nat) [MOD 3] :=
    Nat.ModEq.add (Nat.ModEq.add (hpm3.pow 2) hpm3) (Nat.ModEq.refl 1)
  have hmod3 : (p ^ 2 + p + 1) % 3 = 0 := by
    -- `rwa ... at hsum3` already closed the goal, so the extra `norm_num` reported
    -- "No goals to be solved" (candidate 6266 E01).  `simpa only` does it in one step.
    simpa only [Nat.ModEq] using hsum3
  have hdvd3 : (3 : Nat) ∣ p ^ 2 + p + 1 := Nat.dvd_of_mod_eq_zero hmod3
  refine ⟨hdvd3, ?_⟩
  intro h9
  have hmod9 : (p ^ 2 + p + 1) % 9 = 0 :=
    (@Nat.dvd_iff_mod_eq_zero 9 (p ^ 2 + p + 1)).mp h9
  -- `p ≡ p % 9 (mod 9)` from `Nat.div_add_mod` and `Nat.ModEq.modulus_mul_add`.  Note the
  -- congruence is already in the required orientation; `.symm` reverses it wrongly.
  have hp9 : p ≡ p % 9 [MOD 9] := by
    have h := Nat.ModEq.modulus_mul_add (m := 9) (a := p / 9) (b := p % 9)
    rwa [Nat.div_add_mod] at h
  have hsum9 : p ^ 2 + p + 1 ≡ (p % 9) ^ 2 + p % 9 + 1 [MOD 9] := by
    have hpm3 : p ≡ p % 9 [MOD 9] := hp9
    exact Nat.ModEq.add (Nat.ModEq.add (hpm3.pow 2) hpm3) (Nat.ModEq.refl 1)
  rw [Nat.ModEq] at hsum9
  rw [hsum9] at hmod9
  -- Name the residue WITH its bounds, then split.  `interval_cases` needs the upper bound
  -- `res < 9` in context; that is the whole of the 6254 E02 repair.
  -- `Nat.mod_lt : (x : Nat) -> {y : Nat} -> (hy : 0 < y) -> x % y < y` -- the MODULUS IS
  -- IMPLICIT, so the bound is `Nat.mod_lt _ (by omega)` and NOT `Nat.mod_lt (by omega) 9`
  -- (candidate 6255 E02: "numerals are data in Lean, but the expected type is a
  -- proposition").  And `interval_cases` takes an EXPRESSION or `h : n`, not two proofs
  -- (candidate 6263 E03: "Function expected at hres0, Actual type 0 <= p % 9").
  -- `Nat.mod_lt : (x : Nat) -> {y : Nat} -> (hy : 0 < y) -> x % y < y` -- the MODULUS IS
  -- IMPLICIT.  Both bounds must be NAMED: `interval_cases ... using hl, hu` evaluates the two
  -- hypotheses, and an inline `Nat.zero_le _` is not evaluable (candidate 6266 E02).
  have hres0 : 0 ≤ p % 9 := Nat.zero_le _
  have hres9 : p % 9 < 9 := Nat.mod_lt _ (by omega)
  interval_cases p % 9 using hres0, hres9 <;> norm_num [Nat.not_lt_zero] at hmod9

end Three
end Kernel
end OddPerfectNumber

open OddPerfectNumber.Kernel

theorem solution {p : Nat} (hp4 : 4 <= p) (h1 : p % 3 = 1) :
    (3 : Nat) ∣ p ^ 2 + p + 1 ∧ ¬ (9 : Nat) ∣ p ^ 2 + p + 1 :=
  OddPerfectNumber.Kernel.Three.solution hp4 h1
