-- Prove2me | solution 1 for PrattPart.out_yukon_742b4a5d48a0
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-30T01:01:28.060039+00:00
-- url     : https://prove2.me/submissions/112deb21-5625-4c0b-9763-8e89cd675576

/-
Copyright (c) 2020 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Tactic.ReduceModChar
public import Mathlib.NumberTheory.LucasPrimality


public import Definitions.Def_Yukon_5a1c8f8f8be9100f7eedfb21
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
theorem _root_.solution {p : ℕ} {a : ZMod p} {n : ℕ} (h : PrattPart p a n) :
    ∀ q : ℕ, q.Prime → q ∣ n → a ^ ((p - 1) / q) ≠ 1  := by
  induction h with
  | prime n k nk hprime hpow hnk =>
    subst hnk
    intro q hq hdiv
    cases (Nat.prime_dvd_prime_iff_eq hq hprime).mp (hq.dvd_of_dvd_pow hdiv)
    exact hpow
  | split n l r _ hlr ih₁ ih₂ =>
    subst hlr
    intro q hq hdiv
    rcases hq.dvd_mul.mp hdiv with (hdiv|hdiv)
    · exact ih₁ _ hq hdiv
    · exact ih₂ _ hq hdiv
end
end
