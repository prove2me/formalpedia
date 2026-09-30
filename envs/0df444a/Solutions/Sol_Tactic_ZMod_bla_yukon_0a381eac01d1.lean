-- Prove2me | solution 1 for Tactic.ZMod.bla_yukon_0a381eac01d1
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-30T03:45:55.77137+00:00
-- url     : https://prove2.me/submissions/b15989e5-2892-4bb3-886e-2482a907fa71

/-
Copyright (c) 2020 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Tactic.ReduceModChar
public import Mathlib.NumberTheory.LucasPrimality


@[expose] public section
/-!
# The Lucas test for primes.

This file implements the Lucas test for primes (not to be confused with the Lucas-Lehmer test for
Mersenne primes). A number `a` witnesses that `n` is prime if `a` has order `n-1` in the
multiplicative group of integers mod `n`. This is checked by verifying that `a^(n-1) = 1 (mod n)`
and `a^d ≠ 1 (mod n)` for any divisor `d | n - 1`. This test is the basis of the Pratt primality
certificate.

## TODO

- Bonus: Show the reverse implication i.e. if a number is prime then it has a Lucas witness.
  Use `Units.IsCyclic` from `RingTheory/IntegralDomain` to show the group is cyclic.
- Write a tactic that uses this theorem to generate Pratt primality certificates
- Integrate Pratt primality certificates into the norm_num primality verifier

## Implementation notes

Note that the proof for `lucas_primality` relies on analyzing the multiplicative group
modulo `p`. Despite this, the theorem still holds vacuously for `p = 0` and `p = 1`: In these
cases, we can take `q` to be any prime and see that `hd` does not hold, since `a^((p-1)/q)` reduces
to `1`.
-/

@[expose] public section

section New

-- TODO: port to `Mathlib`?
end New
-- cannot do ^1 correctly it seems?
-- theorem prime_987654319 : Nat.Prime 987654319 := sorry
namespace Tactic

open Lean Meta Simp
open Lean.Elab
open Tactic
open Qq
open Mathlib.Meta.NormNum
theorem ZMod.bla : ∀ {n c : ℕ} (a : ZMod n), c = 1 → IsNat (a ^ (n - 1)) c → a ^ (n - 1) = 1
   := @fun
  | n, _, a, rfl, h => by
    conv_rhs => rw [← Nat.cast_one]
    exact h.out
end Tactic
end
end

public theorem _root_.solution : type_of% @Tactic.ZMod.bla := @Tactic.ZMod.bla
