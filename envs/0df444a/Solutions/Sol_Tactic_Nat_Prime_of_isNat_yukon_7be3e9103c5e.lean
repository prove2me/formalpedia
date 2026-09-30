-- Prove2me | solution 1 for Tactic.Nat.Prime_of_isNat_yukon_7be3e9103c5e
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-30T03:24:31.607178+00:00
-- url     : https://prove2.me/submissions/496984f1-7bea-459d-bcad-e07c38d9b81e

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
-- return q(sorry)
  -- have npred : Q(ℕ) := mkRawNatLit (n.natLit! - 1)
  -- haveI : $n =Q Nat.succ $npred := ⟨⟩
  -- -- haveI : $npred =Q $n - 1 := ⟨⟩
  -- let ⟨c, pc⟩ := evalNatPowMod a' npred n
  -- let pc' : Q(Nat.mod (Nat.pow «$a'» «$npred») «$n» = «$c») := q(sorry)
  -- -- have hc : Q(decide ($c = 1) = true) := (q(Eq.refl true) : Expr)
  -- haveI : $c =Q 1 := ⟨⟩
  -- -- return q(sorry)
  -- return q(ZMod.powEqOfPowMod $a $ha $pc' (.refl _))
-- return q(ZMod.powNeOfPowMod $a $ha $hn $pc $hc)

-- Invariant: n'.natLit! = n
theorem Nat.Prime_of_isNat : ∀ {n n' : ℕ}, IsNat n n' → n'.Prime → n.Prime
   := @fun
  | _, _, ⟨rfl⟩, hp => hp
end Tactic
end
end

public theorem _root_.solution : type_of% @Tactic.Nat.Prime_of_isNat := @Tactic.Nat.Prime_of_isNat
