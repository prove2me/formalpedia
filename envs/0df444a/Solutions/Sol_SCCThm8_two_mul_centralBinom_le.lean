-- Prove2me | solution 1 for SCCThm8.two_mul_centralBinom_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:44:56.945925+00:00
-- url     : https://prove2.me/submissions/3c758ae2-4633-4195-83b4-7c8120957379

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric
public import Theorems.Thm_SCCThm8_centralBinom_succ_lt

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
namespace SCCThm8
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) : 2 * Nat.centralBinom n ≤ 4 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have := centralBinom_succ_lt n
    rw [pow_succ]; omega
end SCCThm8
