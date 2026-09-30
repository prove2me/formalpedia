-- Prove2me | solution 1 for PrattCertificate.out_yukon_b1abd2ed34d1
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-30T01:20:15.141773+00:00
-- url     : https://prove2.me/submissions/8e1c7a10-d311-4667-9f63-6326760f7cd1

/-
Copyright (c) 2020 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Tactic.ReduceModChar
public import Mathlib.NumberTheory.LucasPrimality


public import Definitions.Def_Yukon_92052b9f6262f4f17145e198
public import Definitions.Def_Yukon_78c45b9c719192907ad82297
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
theorem _root_.solution {p : ℕ} (c : PrattCertificate p) : p.Prime  := lucas_primality p c.a c.pow_eq_one c.part.out
end
end
