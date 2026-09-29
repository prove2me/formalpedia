-- Prove2me | solution 1 for WorkbookSyntax.plus_42311
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:07:11.54476+00:00
-- url     : https://prove2.me/submissions/f8743fba-aa53-4fcd-b781-cf29e45a1443

import Mathlib
open Nat
open scoped Nat
set_option autoImplicit false
theorem solution (n : ℕ) : ∑ k ∈ divisors n, φ k = n := by
  exact Nat.sum_totient n
example : (∀ n : ℕ, ∑ k ∈ divisors n, φ k = n) := @solution
#print axioms solution
