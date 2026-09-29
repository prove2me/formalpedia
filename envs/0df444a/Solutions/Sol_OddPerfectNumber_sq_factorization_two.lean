-- Prove2me | solution 1 for OddPerfectNumber.sq_factorization_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T10:54:13.013776+00:00
-- url     : https://prove2.me/submissions/9c24199d-816b-4a2f-8544-259c304b24ef

import Mathlib

-- Pointwise reading of Nat.factorization_pow at exponent 2.
theorem solution {m q : Nat} :
    (m ^ 2).factorization q = 2 * m.factorization q := by
  have h := Nat.factorization_pow m 2
  have hq := congrArg (fun f : ℕ →₀ ℕ => f q) h
  simpa only [Finsupp.smul_apply, smul_eq_mul] using hq
