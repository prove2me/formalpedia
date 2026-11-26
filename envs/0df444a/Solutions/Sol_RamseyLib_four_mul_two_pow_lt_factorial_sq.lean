-- Prove2me | solution 1 for RamseyLib.four_mul_two_pow_lt_factorial_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:16:02.489905+00:00
-- url     : https://prove2.me/submissions/65ffb6fb-e4ef-49d3-a3c8-729ee3627f69

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyLib
namespace RamseyLib
theorem _root_.solution (k : ℕ) (hk : 3 ≤ k) : 4 * 2 ^ k < (k.factorial) ^ 2 := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Nat.factorial_succ, pow_succ, mul_pow]
    have h2 : 2 ≤ (k + 1) ^ 2 := by nlinarith
    nlinarith [Nat.mul_le_mul_right (k.factorial ^ 2) h2]
end RamseyLib
